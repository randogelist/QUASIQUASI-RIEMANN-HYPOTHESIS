/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import RiemannHypothesis.ComplexAnalysis.LogDerivative

/-!
# HadamardProduct.GenusOne

The genus-one Weierstrass factor `E₁(s/ρ) = (1 - s/ρ)·exp(s/ρ)` and its logarithmic
derivative, together with the small bridge lemmas relating this repository's
`logDerivativeResponse` to Mathlib's `logDeriv`. Identity content only — no sign or
zero-free claims.

## Main declarations

* `hadamardGenus1Factor`, `_ne_zero`, `_differentiableAt`, `_zero` — the factor and its
  basic analytic facts.
* `logDerivativeResponse_eq_logDeriv`, `logDerivativeResponse_mul_eq_add`,
  `deriv_div_eq_zero_of_logDerivativeResponse_eq` — `logDerivativeResponse` ↔ `logDeriv`.
* `logDeriv_hadamardGenus1Factor` — the classical `1/(s-ρ) + 1/ρ`.
-/

namespace OverflowResidueRH

/-- **Genus-1 Hadamard factor** `E₁(s/ρ) = (1 - s/ρ) · exp(s/ρ)`. -/
noncomputable def hadamardGenus1Factor (ρ s : ℂ) : ℂ :=
  (1 - s / ρ) * Complex.exp (s / ρ)

/-- ⭐ **PROVED — genus-1 factor non-vanishing when `s ≠ ρ` and `ρ ≠ 0`.** -/
lemma hadamardGenus1Factor_ne_zero {ρ s : ℂ} (hρ : ρ ≠ 0) (hsρ : s ≠ ρ) :
    hadamardGenus1Factor ρ s ≠ 0 := by
  unfold hadamardGenus1Factor
  apply mul_ne_zero
  · intro h
    have h1 : s / ρ = 1 := by linear_combination -h
    have h2 : s = ρ := by
      have := h1
      field_simp at this
      exact this
    exact hsρ h2
  · exact Complex.exp_ne_zero _

/-- ⭐ **PROVED — genus-1 factor is differentiable everywhere.** -/
lemma hadamardGenus1Factor_differentiableAt (ρ s : ℂ) :
    DifferentiableAt ℂ (hadamardGenus1Factor ρ) s := by
  unfold hadamardGenus1Factor
  have h_left : DifferentiableAt ℂ (fun y : ℂ => 1 - y / ρ) s :=
    (differentiableAt_const _).sub (differentiableAt_fun_id.div_const _)
  have h_inner : DifferentiableAt ℂ (fun y : ℂ => y / ρ) s :=
    differentiableAt_fun_id.div_const _
  have h_right : DifferentiableAt ℂ (fun y : ℂ => Complex.exp (y / ρ)) s :=
    h_inner.cexp
  exact h_left.mul h_right

/-- ⭐ **PROVED — every genus-one Hadamard factor is normalized to `1`
at the origin.** -/
theorem hadamardGenus1Factor_zero (ρ : ℂ) :
    hadamardGenus1Factor ρ 0 = 1 := by
  simp [hadamardGenus1Factor]

/-- ⭐ **PROVED — bridge between `logDeriv` (Mathlib) and
`logDerivativeResponse` (this repository).** Definitionally equal. -/
theorem logDerivativeResponse_eq_logDeriv (f : ℂ → ℂ) (z : ℂ) :
    logDerivativeResponse f z = logDeriv f z := rfl

/-- 🌟🌟 **PROVED — product rule for `logDerivativeResponse`.** -/
theorem logDerivativeResponse_mul_eq_add
    {f g : ℂ → ℂ} {s : ℂ}
    (hf_diff : DifferentiableAt ℂ f s)
    (hg_diff : DifferentiableAt ℂ g s)
    (hf_ne : f s ≠ 0)
    (hg_ne : g s ≠ 0) :
    logDerivativeResponse (fun w : ℂ => f w * g w) s
      = logDerivativeResponse f s + logDerivativeResponse g s := by
  rw [logDerivativeResponse_eq_logDeriv,
      logDeriv_mul s hf_ne hg_ne hf_diff hg_diff,
      ← logDerivativeResponse_eq_logDeriv (f := f),
      ← logDerivativeResponse_eq_logDeriv (f := g)]

/-- 🌟🌟🌟 **PROVED — equal log-derivatives force a quotient derivative
to vanish.** Once two nonzero differentiable functions have the same
logarithmic derivative at `s`, the quotient `f/g` has derivative `0`
at `s`. -/
theorem deriv_div_eq_zero_of_logDerivativeResponse_eq
    {f g : ℂ → ℂ} {s : ℂ}
    (hf_diff : DifferentiableAt ℂ f s)
    (hg_diff : DifferentiableAt ℂ g s)
    (hf_ne : f s ≠ 0)
    (hg_ne : g s ≠ 0)
    (hlog : logDerivativeResponse f s = logDerivativeResponse g s) :
    deriv (fun w : ℂ => f w / g w) s = 0 := by
  unfold logDerivativeResponse at hlog
  rw [deriv_fun_div hf_diff hg_diff hg_ne]
  field_simp [hf_ne, hg_ne] at hlog ⊢
  ring_nf at hlog ⊢
  exact sub_eq_zero.mpr hlog

/-- 🌟🌟🌟 **PROVED — per-factor log-derivative of the genus-1
Hadamard factor.** `logDeriv ((1 - ·/ρ) · exp(·/ρ)) s = 1/(s-ρ) + 1/ρ`. -/
theorem logDeriv_hadamardGenus1Factor {ρ s : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDeriv (hadamardGenus1Factor ρ) s = 1 / (s - ρ) + 1 / ρ := by
  have h_left_diff : DifferentiableAt ℂ (fun y : ℂ => 1 - y/ρ) s :=
    (differentiableAt_const _).sub (differentiableAt_fun_id.div_const _)
  have h_inner_diff : DifferentiableAt ℂ (fun y : ℂ => y/ρ) s :=
    differentiableAt_fun_id.div_const _
  have h_right_diff : DifferentiableAt ℂ (fun y : ℂ => Complex.exp (y/ρ)) s :=
    h_inner_diff.cexp
  have hsmρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have h_left_ne : (1 : ℂ) - s/ρ ≠ 0 := by
    intro h
    have h1 : s/ρ = 1 := by linear_combination -h
    apply hs
    field_simp at h1
    exact h1
  have h_exp_ne : Complex.exp (s/ρ) ≠ 0 := Complex.exp_ne_zero _
  have h_deriv_inner : deriv (fun y : ℂ => y/ρ) s = 1/ρ := by
    rw [deriv_div_const, deriv_id'']
  have h_deriv_left : deriv (fun y : ℂ => 1 - y/ρ) s = -(1/ρ) := by
    rw [deriv_fun_sub (differentiableAt_const _) (differentiableAt_fun_id.div_const _),
        deriv_const, h_deriv_inner]
    ring
  have h_deriv_right : deriv (fun y : ℂ => Complex.exp (y/ρ)) s
      = Complex.exp (s/ρ) * (1/ρ) := by
    rw [deriv_cexp h_inner_diff, h_deriv_inner]
  have hρs : ρ - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  rw [logDeriv_apply]
  unfold hadamardGenus1Factor
  rw [deriv_fun_mul h_left_diff h_right_diff, h_deriv_left, h_deriv_right]
  rw [show -(1 / ρ) * Complex.exp (s / ρ)
            + (1 - s / ρ) * (Complex.exp (s / ρ) * (1 / ρ))
          = Complex.exp (s / ρ) * (-(1 / ρ) + (1 - s / ρ) * (1 / ρ)) from by ring,
      show (1 - s / ρ) * Complex.exp (s / ρ)
          = Complex.exp (s / ρ) * (1 - s / ρ) from by ring,
      mul_div_mul_left _ _ h_exp_ne]
  rw [show -(1 / ρ) + (1 - s / ρ) * (1 / ρ) = -s / ρ ^ 2 from by
        field_simp; ring]
  rw [show (1 : ℂ) - s / ρ = (ρ - s) / ρ from by field_simp]
  field_simp
  ring

/-- 🌟🌟🌟 **PROVED — per-factor `logDerivativeResponse` of the genus-1
Hadamard factor.** Same identity under the definitional bridge. -/
theorem logDerivativeResponse_hadamardGenus1Factor
    {ρ s : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDerivativeResponse (hadamardGenus1Factor ρ) s = 1 / (s - ρ) + 1 / ρ := by
  rw [logDerivativeResponse_eq_logDeriv]
  exact logDeriv_hadamardGenus1Factor hρ hs

/-- ⭐ **PROVED — genus-1 factor vanishes at its own zero `s = ρ`.** -/
lemma hadamardGenus1Factor_self_eq_zero
    {ρ : ℂ} (hρ : ρ ≠ 0) :
    hadamardGenus1Factor ρ ρ = 0 := by
  unfold hadamardGenus1Factor
  simp [div_self hρ]

end OverflowResidueRH
