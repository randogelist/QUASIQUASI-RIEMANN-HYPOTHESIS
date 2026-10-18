/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Tactic.Ring
import RiemannHypothesis.Xi.Definitions
import RiemannHypothesis.GammaCancellation.PoleSet
import RiemannHypothesis.GammaCancellation.CompletedZeta

/-!
# GammaCancellation.TextbookXi

The raw Γ-based completed-ξ function `completedXiFunction` and its behaviour at the
Γ-pole pullback. The textbook formula

  `ξ(s) = ½·s·(s−1)·π^(−s/2)·Γ(s/2)·ζ(s)`

carries the `Γ(s/2)` factor literally, so it *vanishes* at every Γ-pole pullback point,
and away from those points it agrees with Mathlib's entire `entireRiemannXi`.

## Main declarations

* `rawCompletedXiFormula`, `completedXiFunction_eq_rawFormula` — the formula, `rfl`.
* `completedXiVanishesOnGammaPolePullback` — raw ξ vanishes on the Γ-pole pullback.
* `completedXiNonzeroExcludesGammaPole` — contrapositive: nonzero raw ξ avoids Γ-poles.
* `completedXiRawEntireXiOffPolePointwiseFormula` — raw ξ `=` entire ξ off Γ-poles
  (away from `s = 1`), assembled from the `CompletedZeta` identities.
* `rawCompletedXiCorrectness` — the bundled unconditional correctness package.
-/

namespace OverflowResidueRH

open Complex

/-- **Raw completed-ξ formula** (matches `completedXiFunction` definition). -/
noncomputable def rawCompletedXiFormula (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)
    * Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))
    * Complex.Gamma (s / 2)
    * riemannZeta s

/-- ⭐ **PROVED — `completedXiFunction = rawCompletedXiFormula` by `rfl`.** -/
theorem completedXiFunction_eq_rawFormula (s : ℂ) :
    completedXiFunction s = rawCompletedXiFormula s := rfl

/-- ⭐ **PROVED — `completedXiFunction 1 = 0`.** -/
theorem completedXiFunction_one_eq_zero : completedXiFunction 1 = 0 := by
  unfold completedXiFunction
  ring

/-- 🌟🌟🌟 **PROVED — raw completed ξ vanishes when `s/2 = -n`.**
Direct application of `Complex.Gamma_neg_nat_eq_zero`. -/
theorem completedXiFunction_vanishes_of_half_eq_neg_nat
    {s : ℂ} {n : ℕ} (hs : s / 2 = -((n : ℂ))) :
    completedXiFunction s = 0 := by
  rw [completedXiFunction_eq_rawFormula]
  unfold rawCompletedXiFormula
  rw [hs, Complex.Gamma_neg_nat_eq_zero]
  ring

/-- 📦 **`CompletedXiVanishesOnGammaPolePullback`** — raw completed ξ
vanishes at Γ-pole-pullback points. -/
structure CompletedXiVanishesOnGammaPolePullback : Prop where
  vanishes :
    ∀ s : ℂ,
      s / 2 ∈ gammaPoleSet →
      completedXiFunction s = 0

/-- 🌟🌟🌟🌟 **PROVED unconditionally.** -/
theorem completedXiVanishesOnGammaPolePullback :
    CompletedXiVanishesOnGammaPolePullback := by
  refine ⟨?_⟩
  intro s hsPole
  obtain ⟨n, hn⟩ := hsPole
  exact completedXiFunction_vanishes_of_half_eq_neg_nat hn

/-- 📦 **`CompletedXiNonzeroExcludesGammaPole`** — at any nonzero
completed-ξ point, `s/2` is not a Γ pole. -/
structure CompletedXiNonzeroExcludesGammaPole : Prop where
  not_gamma_pole :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      s / 2 ∉ gammaPoleSet

/-- ⭐ **PROVED — nonzero exclusion from vanishing.** -/
theorem CompletedXiNonzeroExcludesGammaPole.of_vanishes
    (H : CompletedXiVanishesOnGammaPolePullback) :
    CompletedXiNonzeroExcludesGammaPole := by
  refine ⟨?_⟩
  intro s hs hpole
  exact hs (H.vanishes s hpole)

/-- 🌟🌟 **PROVED — `CompletedXiNonzeroExcludesGammaPole`
unconditionally.** -/
theorem completedXiNonzeroExcludesGammaPole :
    CompletedXiNonzeroExcludesGammaPole :=
  CompletedXiNonzeroExcludesGammaPole.of_vanishes
    completedXiVanishesOnGammaPolePullback

/-- 📦 **`CompletedXiRawEntireXiOffPolePointwiseFormula`** — pointwise
off-pole identity. Requires `s ≠ 1` because `entireRiemannXi 1 = 1/2`
while `completedXiFunction 1 = 0` (the `+ 1/2` correction in
`entireRiemannXi`'s definition kicks in when the `s·(s-1)` factor
vanishes). -/
structure CompletedXiRawEntireXiOffPolePointwiseFormula : Prop where
  pointwise_eq :
    ∀ s : ℂ,
      s ≠ 1 →
      s / 2 ∉ gammaPoleSet →
      completedXiFunction s = entireRiemannXi s

/-- 🌟🌟 **PROVED — raw completed ξ formula in terms of
`completedRiemannZeta`** (off Γ poles). -/
theorem rawCompletedXiFormula_eq_completedZeta
    (HzetaRaw : CompletedRiemannZetaRawOffPoleFormula)
    {s : ℂ} (hsPole : s / 2 ∉ gammaPoleSet) :
    rawCompletedXiFormula s
      = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  unfold rawCompletedXiFormula
  rw [HzetaRaw.eq_raw s hsPole]
  ring

/-- 🌟🌟🌟 **PROVED — `CompletedXiRawEntireXiOffPolePointwiseFormula`
from zeta formula identities.** -/
theorem CompletedXiRawEntireXiOffPolePointwiseFormula.of_completedZetaIdentities
    (HzetaRaw : CompletedRiemannZetaRawOffPoleFormula)
    (Hzeta0 : CompletedRiemannZetaZeroCorrectionFormula)
    (Hxi : EntireRiemannXiFormulaSource) :
    CompletedXiRawEntireXiOffPolePointwiseFormula := by
  refine ⟨?_⟩
  intro s hs1 hsPole
  have hs0 : s ≠ 0 := by
    intro hs
    apply hsPole
    rw [hs]
    exact ⟨0, by simp⟩
  calc completedXiFunction s
      = rawCompletedXiFormula s := completedXiFunction_eq_rawFormula s
    _ = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s :=
        rawCompletedXiFormula_eq_completedZeta HzetaRaw hsPole
    _ = (1 / 2 : ℂ) * s * (s - 1)
          * (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) := by
        rw [Hzeta0.correction s]
    _ = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2 :=
        xi_completedZeta_correction_algebra hs0 hs1
    _ = entireRiemannXi s := (Hxi.formula s).symm

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — the raw completed-ξ function
agrees pointwise with Mathlib's `entireRiemannXi` off Γ-poles and away
from `s = 1`. -/
theorem completedXiRawEntireXiOffPolePointwiseFormula :
    CompletedXiRawEntireXiOffPolePointwiseFormula :=
  CompletedXiRawEntireXiOffPolePointwiseFormula.of_completedZetaIdentities
    completedRiemannZetaRawOffPoleFormula
    completedRiemannZetaZeroCorrectionFormula
    entireRiemannXiFormulaSource

/-- 📦 **`RawCompletedXiCorrectness`** — bundles the two Γ-cancellation
facts: nonzero raw ξ avoids Γ-poles, and the off-pole pointwise formula
identity (stated with the `s ≠ 1` exclusion inline). -/
structure RawCompletedXiCorrectness : Prop where
  nonzero_excludes_gammaPole : CompletedXiNonzeroExcludesGammaPole
  offPole_eq :
    ∀ s : ℂ,
      s ≠ 1 →
      s / 2 ∉ gammaPoleSet →
      completedXiFunction s = entireRiemannXi s

/-- 🌟🌟 **PROVED — `RawCompletedXiCorrectness` from the two
pointwise formula targets.** -/
theorem RawCompletedXiCorrectness.of_pointwise
    (Hvanish : CompletedXiVanishesOnGammaPolePullback)
    (Hformula : CompletedXiRawEntireXiOffPolePointwiseFormula) :
    RawCompletedXiCorrectness :=
  { nonzero_excludes_gammaPole :=
      CompletedXiNonzeroExcludesGammaPole.of_vanishes Hvanish
    offPole_eq := Hformula.pointwise_eq }

/-- 🌟🌟🌟🌟 **PROVED unconditionally** — the complete raw completed-ξ
correctness package. -/
theorem rawCompletedXiCorrectness :
    RawCompletedXiCorrectness :=
  RawCompletedXiCorrectness.of_pointwise
    completedXiVanishesOnGammaPolePullback
    completedXiRawEntireXiOffPolePointwiseFormula

end OverflowResidueRH
