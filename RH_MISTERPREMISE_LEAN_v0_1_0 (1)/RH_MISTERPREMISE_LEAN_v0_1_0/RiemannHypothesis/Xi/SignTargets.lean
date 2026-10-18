/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Analytic.Uniqueness
import RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import RiemannHypothesis.ComplexAnalysis.LogDerivative
import RiemannHypothesis.RealZeros.Engine
import RiemannHypothesis.RealZeros.EntireFunctions
import RiemannHypothesis.Xi.Definitions
import RiemannHypothesis.Xi.Pullback
import RiemannHypothesis.Xi.FunctionalEquation

/-!
# Sign conditions for the pullback logarithmic derivative

The named sign conditions equivalent to the Riemann Hypothesis for the
textbook pullback `Ξ`, and the bridges between them:

* `XiPullback.AntiHerglotzSign` — `Im Λ[Ξ] ≤ 0` on the upper half-plane
  (the single genuinely open analytic statement);
* `XiPullback.HerglotzSign` — its Pick/Nevanlinna dual;
* `CompletedXi.leftHalfPlaneLogDerivSign` — the s-plane reformulation
  `Re Λ[ξ] ≤ 0` on `Re s < ½`.

The capstone theorems package the regularity + analytic-factorization +
sign inputs into "every zero of `Ξ` is real".
-/

namespace OverflowResidueRH

open Complex Filter Topology

/-- **Herglotz upper-half-plane sign law.** `Im(R z) ≥ 0` on `Im z > 0`.
The classical Pick/Nevanlinna sign — `R` maps the upper half-plane into
the closed upper half-plane. -/
def HerglotzUHP (R : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.im → 0 ≤ (R z).im

/-- **General dualization.** `R` is anti-Herglotz iff `−R` is Herglotz. -/
theorem negHerglotzUHP_iff_antiHerglotzUHP (R : ℂ → ℂ) :
    HerglotzUHP (fun z => -(R z)) ↔ AntiHerglotzUHP R := by
  unfold HerglotzUHP AntiHerglotzUHP
  constructor
  · intro h z hz
    have h' := h z hz
    simp only [Complex.neg_im] at h'
    linarith
  · intro h z hz
    have h' := h z hz
    simp only [Complex.neg_im]
    linarith

/-- **The xi anti-Herglotz sign condition.** `Im(Λ[Ξ] z) ≤ 0` for every `z`
in the open upper half-plane. The single genuinely open analytic content of
the programme. -/
def XiPullback.AntiHerglotzSign : Prop :=
  AntiHerglotzUHP (logDerivativeResponse XiPullback)

/-- **The xi Herglotz sign condition.** The Pick/Nevanlinna dual: `−Λ[Ξ]`
is Herglotz on the upper half-plane. -/
def XiPullback.HerglotzSign : Prop :=
  HerglotzUHP (fun z => -(logDerivativeResponse XiPullback z))

/-- The two pullback sign conditions are equivalent via negation. -/
theorem XiPullback.HerglotzSign_iff_AntiHerglotzSign :
    XiPullback.HerglotzSign ↔ XiPullback.AntiHerglotzSign :=
  negHerglotzUHP_iff_antiHerglotzUHP _

/-- **s-plane reformulation.** Under `s = ½ + i·z`, the upper half-plane
`Im z > 0` corresponds to the open left half-strip `Re s < ½`, and the chain
rule turns the anti-Herglotz condition into `Re(Λ[ξ](s)) ≤ 0` there. The
natural form for attacks via the explicit ξ formula or digamma decomposition. -/
def CompletedXi.leftHalfPlaneLogDerivSign : Prop :=
  ∀ s : ℂ, s.re < (1 / 2 : ℝ) →
    ((deriv completedXiFunction s) / completedXiFunction s).re ≤ 0

/-- ⭐ **PROVED — s-plane sign ⟹ z-plane anti-Herglotz.**
Given left-half-plane differentiability of `ξ` and the s-plane sign
condition `Re(ξ'/ξ(s)) ≤ 0` for `Re s < ½`, the z-plane condition
`Im(Λ[Ξ](z)) ≤ 0` for `Im z > 0` follows. At zeros of `Ξ`, the totalized
`Λ[Ξ] = 0/0 = 0` makes the inequality trivially `0 ≤ 0`. -/
theorem XiPullback.AntiHerglotzSign_of_leftHalfPlaneLogDerivSign
    (hdiff : CompletedXiDifferentiableOnLeftHalfPlane)
    (h : CompletedXi.leftHalfPlaneLogDerivSign) :
    XiPullback.AntiHerglotzSign := by
  intro z hz
  have hs_re : ((1 / 2 : ℂ) + Complex.I * z).re < (1 / 2 : ℝ) := by
    rw [critical_shift_re]
    linarith
  by_cases hXi : XiPullback z = 0
  · -- vacuous: 0/0 = 0 by Lean convention, so (Λ[Ξ] z).im = 0 ≤ 0
    change (logDerivativeResponse XiPullback z).im ≤ 0
    unfold logDerivativeResponse
    rw [hXi, div_zero]
    exact le_of_eq Complex.zero_im
  · -- chain rule, then Im(I · w) = Re(w), then apply the s-plane hypothesis
    have hxi_diff := hdiff _ hs_re
    rw [XiPullback_logDeriv_chain_rule hxi_diff]
    rw [Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, zero_add, one_mul]
    exact h _ hs_re

/-- ⭐ **PROVED — pullback real-zero data from its three analytic inputs.**
Packages completed-xi regularity, the analytic zero-factorization
hypothesis, and the anti-Herglotz sign condition into an
`AntiHerglotzReflectionData` for `Ξ`:

  • `poleWitness` from the factorization hypothesis (via the entire-function
    pipeline in `RealZeros.EntireFunctions`);
  • `conjugationSymmetry` from `XiPullback_schwarz`;
  • `antiHerglotz` from the supplied sign condition. -/
noncomputable def XiPullback.antiHerglotzReflectionData_of_regularity_factorization_sign
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (Hsign : XiPullback.AntiHerglotzSign) :
    AntiHerglotzReflectionData where
  F := XiPullback
  R := logDerivativeResponse XiPullback
  poleWitness :=
    entireLocalPoleDecomposition_gives_poleWitness
      (entireZeroFactorization_gives_EntireLocalPoleDecompositionHypothesis Hfac)
  antiHerglotz := Hsign
  conjugationSymmetry := XiPullback_schwarz Hreg

/-- ⭐ **PROVED — RH-facing capstone (conditional on the three inputs).**
Every zero of `Ξ` is real, given completed-xi regularity, the analytic
zero-factorization hypothesis, and the anti-Herglotz sign condition. The
three hypotheses isolate exactly the remaining open content. -/
theorem XiPullback.zeros_real_of_regularity_factorization_sign
    (Hreg : CompletedXiRegularity)
    (Hfac : EntireZeroFactorizationHypothesis XiPullback)
    (Hsign : XiPullback.AntiHerglotzSign) :
    ∀ ρ : ℂ, XiPullback ρ = 0 → ρ.im = 0 :=
  (XiPullback.antiHerglotzReflectionData_of_regularity_factorization_sign
    Hreg Hfac Hsign).zeros_real

-- =====================================================================
-- Mathlib-grounded entire ξ: sign conditions and RH-facing capstones
-- =====================================================================

/-- **Entire-ξ pullback anti-Herglotz sign condition.** -/
def EntireXiPullback.AntiHerglotzSign : Prop :=
  AntiHerglotzUHP (logDerivativeResponse EntireXiPullback)

/-- **s-plane sign condition for the Mathlib-grounded ξ.**
`Re(ξ'(s)/ξ(s)) ≤ 0` for `Re s < ½`. -/
def EntireXi.leftHalfPlaneLogDerivSign : Prop :=
  ∀ s : ℂ, s.re < (1 / 2 : ℝ) →
    ((deriv entireRiemannXi s) / entireRiemannXi s).re ≤ 0

/-- ⭐ **PROVED — s-plane sign ⟹ z-plane anti-Herglotz (Mathlib-grounded).** -/
theorem EntireXiPullback.AntiHerglotzSign_of_leftHalfPlaneLogDerivSign
    (h : EntireXi.leftHalfPlaneLogDerivSign) :
    EntireXiPullback.AntiHerglotzSign := by
  intro z hz
  have hs_re : ((1 / 2 : ℂ) + Complex.I * z).re < (1 / 2 : ℝ) := by
    rw [critical_shift_re]; linarith
  by_cases hXi : EntireXiPullback z = 0
  · change (logDerivativeResponse EntireXiPullback z).im ≤ 0
    unfold logDerivativeResponse
    rw [hXi, div_zero]
    exact le_of_eq Complex.zero_im
  · rw [EntireXiPullback_logDeriv_chain_rule]
    rw [Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, zero_add, one_mul]
    exact h _ hs_re

/-- ⭐ **PROVED — `EntireXiPullback` factorization hypothesis from
analyticity + non-triviality.** Feeds the analytic discharge in
`RealZeros.EntireFunctions`; non-triviality + connectedness rules out a
local identical-zero via the isolated-zeros principle. -/
theorem EntireZeroFactorizationHypothesis_EntireXiPullback
    (h_nontrivial : ∃ z : ℂ, EntireXiPullback z ≠ 0) :
    EntireZeroFactorizationHypothesis EntireXiPullback := by
  refine entireZeroFactorization_of_analytic
    (entireAnalyticZerosAdmitFactorization_holds EntireXiPullback) ?_
  intro ρ _hρ_zero _hρ_im
  refine ⟨EntireXiPullback_analyticAt ρ, ?_⟩
  intro hev
  obtain ⟨w, hw⟩ := h_nontrivial
  apply hw
  have h_on : AnalyticOnNhd ℂ EntireXiPullback Set.univ :=
    fun z _ => EntireXiPullback_analyticAt z
  have hPre : IsPreconnected (Set.univ : Set ℂ) := isPreconnected_univ
  have hf_eq_zero : EntireXiPullback =ᶠ[𝓝 ρ] 0 := by
    filter_upwards [hev] with z hz
    simpa using hz
  have heq : Set.EqOn EntireXiPullback 0 Set.univ :=
    h_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero hPre
      (Set.mem_univ ρ) hf_eq_zero
  simpa using heq (Set.mem_univ w)

/-- ⭐ **PROVED — entire-ξ real-zero data from regularity, non-triviality,
and the anti-Herglotz sign condition.** -/
noncomputable def EntireXiPullback.antiHerglotzReflectionData
    (H : EntireRiemannXiRegularity)
    (h_nontrivial : ∃ z : ℂ, EntireXiPullback z ≠ 0)
    (Hsign : EntireXiPullback.AntiHerglotzSign) :
    AntiHerglotzReflectionData where
  F := EntireXiPullback
  R := logDerivativeResponse EntireXiPullback
  poleWitness :=
    entireLocalPoleDecomposition_gives_poleWitness
      (entireZeroFactorization_gives_EntireLocalPoleDecompositionHypothesis
        (EntireZeroFactorizationHypothesis_EntireXiPullback h_nontrivial))
  antiHerglotz := Hsign
  conjugationSymmetry := EntireXiPullback_schwarz H

/-- Every zero of the Mathlib-grounded `EntireXiPullback` is real, given
regularity, nontriviality, and the left-half-plane sign condition. -/
theorem EntireXiPullback.zeros_real_of_regularity_and_sign
    (H : EntireRiemannXiRegularity)
    (h_nontrivial : ∃ z : ℂ, EntireXiPullback z ≠ 0)
    (h_sign : EntireXi.leftHalfPlaneLogDerivSign) :
    ∀ ρ : ℂ, EntireXiPullback ρ = 0 → ρ.im = 0 :=
  (EntireXiPullback.antiHerglotzReflectionData H h_nontrivial
    (EntireXiPullback.AntiHerglotzSign_of_leftHalfPlaneLogDerivSign
      h_sign)).zeros_real

/-- Schwarz reflection, nontriviality, and the sign condition imply real
zeros of the pullback. -/
theorem EntireXiPullback.zeros_real_of_schwarz_and_sign
    (hsch : EntireXi.schwarzReflection)
    (h_nontrivial : ∃ z : ℂ, EntireXiPullback z ≠ 0)
    (h_sign : EntireXi.leftHalfPlaneLogDerivSign) :
    ∀ ρ : ℂ, EntireXiPullback ρ = 0 → ρ.im = 0 :=
  EntireXiPullback.zeros_real_of_regularity_and_sign
    (EntireRiemannXiRegularity_of_schwarz hsch) h_nontrivial h_sign

/-- `EntireXiPullback` is not identically zero. Witness
`z = -I/2`, which sends the critical shift to `s = 1`, where
`entireRiemannXi 1 = ½·1·0·completedRiemannZeta₀ 1 + ½ = ½ ≠ 0`. -/
theorem EntireXiPullback_nontrivial_holds : EntireXiPullback_nontrivial := by
  refine ⟨-Complex.I / 2, ?_⟩
  have h_shift : (1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) = 1 := by
    have h_I2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have h_eq : Complex.I * (-Complex.I / 2)
                  = -((Complex.I * Complex.I) / 2) := by ring
    rw [h_eq, h_I2]
    ring
  unfold EntireXiPullback entireRiemannXi
  rw [h_shift]
  change (1 / 2 : ℂ) * 1 * (1 - 1) * completedRiemannZeta₀ 1 + (1 / 2 : ℂ) ≠ 0
  rw [show (1 : ℂ) - 1 = 0 from by ring]
  ring_nf
  exact (by norm_num : (1 / 2 : ℂ) ≠ 0)

/-- The Hurwitz FE-pair real-lifting hypothesis and the s-plane sign imply
real zeros of the entire-xi pullback. -/
theorem EntireXiPullback.zeros_real_of_hurwitzReality_and_sign
    (h_real : hurwitzEvenFEPair_zero_f_modif_ofReal_target)
    (h_sign : EntireXi.leftHalfPlaneLogDerivSign) :
    ∀ ρ : ℂ, EntireXiPullback ρ = 0 → ρ.im = 0 :=
  EntireXiPullback.zeros_real_of_schwarz_and_sign
    (entireRiemannXi_schwarz_of_hurwitzZero h_real)
    EntireXiPullback_nontrivial_holds h_sign

/-- The s-plane sign condition implies real-rootedness of
`EntireXiPullback`. Schwarz reflection and nontriviality are discharged; the
sign condition is the sole hypothesis. -/
theorem EntireXiPullback.zeros_real_of_sign
    (h_sign : EntireXi.leftHalfPlaneLogDerivSign) :
    ∀ ρ : ℂ, EntireXiPullback ρ = 0 → ρ.im = 0 :=
  EntireXiPullback.zeros_real_of_schwarz_and_sign
    EntireXi.schwarzReflection_holds
    EntireXiPullback_nontrivial_holds h_sign

end OverflowResidueRH
