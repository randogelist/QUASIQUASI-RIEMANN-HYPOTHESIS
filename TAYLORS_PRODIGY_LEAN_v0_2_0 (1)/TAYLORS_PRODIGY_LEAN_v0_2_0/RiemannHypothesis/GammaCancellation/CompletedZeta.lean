/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import RiemannHypothesis.Xi.Definitions
import RiemannHypothesis.GammaCancellation.PoleSet

/-!
# GammaCancellation.CompletedZeta

The Mathlib-grounded identities that drive the Γ-cancellation: away from the Γ-poles,
Mathlib's `completedRiemannZeta` is the raw `π^(-s/2)·Γ(s/2)·ζ(s)` product, and it
relates to the entire `completedRiemannZeta₀` by the standard pole-correction
`completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)`.

## Main declarations

* `completedRiemannZetaRawOffPoleFormula` — Mathlib's completed ζ equals the raw Γ·ζ
  expression off Γ-poles (unconditional).
* `completedRiemannZetaZeroCorrectionFormula` — the `₀` pole-correction (unconditional).
* `entireRiemannXiFormulaSource` — `entireRiemannXi` in closed form (definitional).
* `xi_completedZeta_correction_algebra` — the `+ 1/2` correction algebra, valid for
  `s ≠ 0, 1`.
-/

namespace OverflowResidueRH

open Complex

/-- 📦 **`CompletedRiemannZetaRawOffPoleFormula`** — Mathlib's
`completedRiemannZeta s = π^(-s/2) · Γ(s/2) · ζ(s)` away from Γ poles. -/
structure CompletedRiemannZetaRawOffPoleFormula : Prop where
  eq_raw :
    ∀ s : ℂ,
      s / 2 ∉ gammaPoleSet →
      completedRiemannZeta s
        = Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
          * Complex.Gamma (s / 2) * riemannZeta s

/-- ⭐ **PROVED — off Γ-poles implies `s ≠ 0`.** -/
theorem ne_zero_of_half_not_gammaPole
    {s : ℂ} (hsPole : s / 2 ∉ gammaPoleSet) :
    s ≠ 0 := by
  intro hs
  apply hsPole
  rw [hs]
  exact ⟨0, by simp⟩

/-- ⭐ **PROVED — off Γ-poles implies the Deligne Γ-factor is nonzero.** -/
theorem GammaReal_ne_zero_of_half_not_gammaPole
    {s : ℂ} (hsPole : s / 2 ∉ gammaPoleSet) :
    Gammaℝ s ≠ 0 := by
  intro hG
  rcases Complex.Gammaℝ_eq_zero_iff.mp hG with ⟨n, hn⟩
  apply hsPole
  exact ⟨n, by rw [hn]; ring⟩

/-- ⭐ **PROVED — `Gammaℝ` as the explicit exponential Γ-factor.** -/
theorem GammaReal_eq_exp_gamma (s : ℂ) :
    Gammaℝ s =
      Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
        * Complex.Gamma (s / 2) := by
  rw [Gammaℝ_def]
  congr 1
  rw [Complex.cpow_def_of_ne_zero]
  · congr 1
    rw [Complex.ofReal_log Real.pi_pos.le]
    ring
  · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

/-- 🌟🌟 **PROVED unconditionally** — Mathlib's completed zeta is the
raw Γ·ζ expression off Γ-poles. -/
theorem completedRiemannZetaRawOffPoleFormula :
    CompletedRiemannZetaRawOffPoleFormula := by
  refine ⟨?_⟩
  intro s hsPole
  have hs0 : s ≠ 0 := ne_zero_of_half_not_gammaPole hsPole
  have hG : Gammaℝ s ≠ 0 := GammaReal_ne_zero_of_half_not_gammaPole hsPole
  calc
    completedRiemannZeta s
        = Gammaℝ s * riemannZeta s := by
            have hz := riemannZeta_def_of_ne_zero (s := s) hs0
            rw [hz]
            field_simp [hG]
    _ = Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
          * Complex.Gamma (s / 2) * riemannZeta s := by
            rw [GammaReal_eq_exp_gamma]

/-- 📦 **`CompletedRiemannZetaZeroCorrectionFormula`** — Mathlib's
`completedRiemannZeta_eq` identity. -/
structure CompletedRiemannZetaZeroCorrectionFormula : Prop where
  correction :
    ∀ s : ℂ,
      completedRiemannZeta s
        = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)

/-- 🌟🌟 **PROVED unconditionally** — direct application of
Mathlib's `completedRiemannZeta_eq`. -/
theorem completedRiemannZetaZeroCorrectionFormula :
    CompletedRiemannZetaZeroCorrectionFormula :=
  ⟨completedRiemannZeta_eq⟩

/-- 📦 **`EntireRiemannXiFormulaSource`** — definition-formula for
`entireRiemannXi`. -/
structure EntireRiemannXiFormulaSource : Prop where
  formula :
    ∀ s : ℂ,
      entireRiemannXi s
        = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2

/-- ⭐ **PROVED unconditionally** — `entireRiemannXi` is exactly that
formula by definition. -/
theorem entireRiemannXiFormulaSource :
    EntireRiemannXiFormulaSource := by
  refine ⟨?_⟩
  intro _
  rfl

/-- ⭐ **PROVED — algebra for the ξ correction term**, valid for
`s ≠ 0` and `s ≠ 1`. The identity fails at s = 0 and s = 1 in Lean's
totalized arithmetic (`1/0 = 0`), because the `+ 1/2` correction
kicks in exactly when the `s·(s-1)` factor vanishes. -/
theorem xi_completedZeta_correction_algebra
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    (1 / 2 : ℂ) * s * (s - 1)
        * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s))
      = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2 := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

end OverflowResidueRH
