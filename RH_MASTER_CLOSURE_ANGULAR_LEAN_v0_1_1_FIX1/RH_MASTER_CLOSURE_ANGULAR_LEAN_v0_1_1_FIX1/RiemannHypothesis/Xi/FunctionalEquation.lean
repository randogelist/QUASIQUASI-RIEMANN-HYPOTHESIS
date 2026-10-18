/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import RiemannHypothesis.Xi.Definitions

/-!
# Functional equation and Schwarz reflection for the pullback

The pullback Schwarz reflection `Ξ(z̄) = conj Ξ(z)`, derived from the
completed-xi regularity package (Schwarz reflection of `ξ` together with the
functional equation `ξ(s) = ξ(1 − s)`).

(The Mathlib-grounded entire `ξ` functional equation and the unconditional
Schwarz discharge via the Hurwitz even FE-pair are added later in this file.)
-/

namespace OverflowResidueRH

open Complex

/-- ⭐ **PROVED — pullback Schwarz reflection.** `Ξ(star z) = star (Ξ z)`.

  star(Ξ z) = star (ξ(½ + I·z)) = ξ(star(½ + I·z))          (ξ-Schwarz)
            = ξ((½) − I·star z)                              (critical_shift_star)
            = ξ(1 − ((½) − I·star z)) = ξ((½) + I·star z)    (functional eqn)
            = Ξ(star z). -/
theorem XiPullback_schwarz
    (H : CompletedXiRegularity) :
    ∀ z : ℂ, XiPullback (star z) = star (XiPullback z) := by
  intro z
  unfold XiPullback
  rw [← H.schwarz, critical_shift_star]
  rw [H.functional_equation ((1 / 2 : ℂ) + Complex.I * star z)]
  congr 1
  ring

-- =====================================================================
-- Mathlib-grounded entire ξ: differentiability, functional equation, Schwarz
-- =====================================================================

/-- ⭐ **PROVED — `entireRiemannXi` is differentiable everywhere.**
Polynomial · (entire `completedRiemannZeta₀`) + const. -/
theorem entireRiemannXi_differentiable :
    Differentiable ℂ entireRiemannXi := by
  unfold entireRiemannXi
  have h_poly : Differentiable ℂ
      (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) := by
    exact ((differentiable_const _).mul differentiable_id).mul
      (differentiable_id.sub (differentiable_const _))
  have h_zeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
    differentiable_completedZeta₀
  exact (h_poly.mul h_zeta₀).add (differentiable_const _)

/-- ⭐ **PROVED — functional equation `entireRiemannXi (1 − s) = entireRiemannXi s`.**
Symmetric polynomial prefactor + `completedRiemannZeta₀_one_sub`. -/
theorem entireRiemannXi_one_sub (s : ℂ) :
    entireRiemannXi (1 - s) = entireRiemannXi s := by
  unfold entireRiemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- ⭐ **PROVED — `entireRiemannXi` differentiable at every point.** -/
theorem entireRiemannXi_differentiableAt (s : ℂ) :
    DifferentiableAt ℂ entireRiemannXi s :=
  entireRiemannXi_differentiable s

/-- ⭐ **PROVED — Mathlib-grounded ξ regularity is automatic modulo
Schwarz.** Differentiability and the functional equation come for free;
only Schwarz remains. -/
theorem EntireRiemannXiRegularity_of_schwarz
    (hsch : EntireXi.schwarzReflection) :
    EntireRiemannXiRegularity where
  differentiable := entireRiemannXi_differentiableAt
  schwarz := hsch
  functional_equation := fun s => (entireRiemannXi_one_sub s).symm

/-- ⭐ **PROVED — `EntireXiPullback` is differentiable everywhere.** -/
theorem EntireXiPullback_differentiable :
    Differentiable ℂ EntireXiPullback := by
  intro z
  unfold EntireXiPullback
  have h_inner : DifferentiableAt ℂ
      (fun w : ℂ => (1 / 2 : ℂ) + Complex.I * w) z :=
    (differentiableAt_const _).add
      ((differentiableAt_const _).mul differentiableAt_fun_id)
  have h_outer : DifferentiableAt ℂ entireRiemannXi
      ((1 / 2 : ℂ) + Complex.I * z) :=
    entireRiemannXi_differentiableAt _
  exact h_outer.comp z h_inner

/-- ⭐ **PROVED — `EntireXiPullback` is analytic at every point.** -/
theorem EntireXiPullback_analyticAt (z : ℂ) :
    AnalyticAt ℂ EntireXiPullback z :=
  EntireXiPullback_differentiable.analyticAt z

/-- ⭐ **PROVED — Schwarz reflection for `EntireXiPullback`.** From the
Mathlib-grounded regularity (Schwarz + functional equation). -/
theorem EntireXiPullback_schwarz
    (H : EntireRiemannXiRegularity) :
    ∀ z : ℂ, EntireXiPullback (star z) = star (EntireXiPullback z) := by
  intro z
  unfold EntireXiPullback
  rw [← H.schwarz, critical_shift_star]
  rw [H.functional_equation ((1 / 2 : ℂ) + Complex.I * star z)]
  congr 1
  ring

-- =====================================================================
-- Unconditional Schwarz reflection for `entireRiemannXi`
--   Mellin keystone → Hurwitz even FE-pair → completedRiemannZeta₀ → ξ
-- =====================================================================

open MeasureTheory in
/-- ⭐ **PROVED — Mellin transform of an `ℝ → ℂ`-lifted real function
commutes with conjugation.** For real-valued `f`,
`mellin (ofReal ∘ f) (star s) = star (mellin (ofReal ∘ f) s)`, via
`integral_conj` + `Complex.cpow_conj` (using `(t : ℂ).arg = 0 ≠ π` for `t > 0`). -/
theorem mellin_star_ofReal (f : ℝ → ℝ) (s : ℂ) :
    mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) (star s)
      = star (mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) s) := by
  unfold mellin
  rw [show star (∫ t in Set.Ioi (0 : ℝ),
        ((t : ℂ) ^ (s - 1) • ((f t : ℝ) : ℂ)))
      = ∫ t in Set.Ioi (0 : ℝ),
        star ((t : ℂ) ^ (s - 1) • ((f t : ℝ) : ℂ))
      from (integral_conj
        (f := fun t : ℝ => (t : ℂ) ^ (s - 1) • ((f t : ℝ) : ℂ))
        (μ := MeasureTheory.volume.restrict (Set.Ioi 0))).symm]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  change (t : ℂ) ^ (star s - 1) • ((f t : ℝ) : ℂ)
        = star ((t : ℂ) ^ (s - 1) • ((f t : ℝ) : ℂ))
  have htpos : 0 < t := ht
  have h_arg : ((t : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg htpos.le]
    exact (Real.pi_pos.ne').symm
  rw [Complex.star_def, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal]
  congr 1
  have h_cpow := Complex.cpow_conj (t : ℂ) (s - 1) h_arg
  rw [Complex.conj_ofReal] at h_cpow
  have h_sub : (starRingEnd ℂ) (s - 1) = (starRingEnd ℂ) s - 1 := by
    rw [map_sub, map_one]
  rw [← h_sub]
  exact h_cpow

/-- ⭐ **PROVED — abstract FE-pair lift.** If a `WeakFEPair ℂ` has its
`f_modif` field equal to the `ofReal` lift of a real-valued function,
then its `Λ₀` commutes with `star`. -/
theorem WeakFEPair_Λ₀_star_of_f_modif_ofReal
    (P : WeakFEPair ℂ) (φ : ℝ → ℝ)
    (h : ∀ x : ℝ, P.f_modif x = ((φ x : ℝ) : ℂ))
    (s : ℂ) :
    P.Λ₀ (star s) = star (P.Λ₀ s) := by
  unfold WeakFEPair.Λ₀
  have h_eq : P.f_modif = fun t : ℝ => ((φ t : ℝ) : ℂ) := funext h
  rw [h_eq]
  exact mellin_star_ofReal φ s

/-- **Hypothesis — `hurwitzEvenFEPair 0` has real-valued `f_modif`.**
Discharged unconditionally below by `hurwitzEvenFEPair_zero_f_modif_ofReal_holds`. -/
def hurwitzEvenFEPair_zero_f_modif_ofReal_target : Prop :=
  ∃ φ : ℝ → ℝ, ∀ x : ℝ,
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x = ((φ x : ℝ) : ℂ)

/-- ⭐ **PROVED — `completedHurwitzZetaEven₀ 0` Schwarz, modulo the FE-pair
real-lifting hypothesis.** -/
theorem completedHurwitzZetaEven₀_zero_star
    (h_real : hurwitzEvenFEPair_zero_f_modif_ofReal_target) (s : ℂ) :
    HurwitzZeta.completedHurwitzZetaEven₀ 0 (star s)
      = star (HurwitzZeta.completedHurwitzZetaEven₀ 0 s) := by
  obtain ⟨φ, hφ⟩ := h_real
  unfold HurwitzZeta.completedHurwitzZetaEven₀
  have h_two_star : star ((2 : ℂ)) = (2 : ℂ) := by
    rw [Complex.star_def,
        show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) from by norm_num,
        Complex.conj_ofReal]
  rw [show (star s : ℂ) / 2 = star (s / 2) from by rw [star_div₀, h_two_star]]
  rw [WeakFEPair_Λ₀_star_of_f_modif_ofReal _ φ hφ (s / 2)]
  rw [star_div₀, h_two_star]

/-- ⭐ **PROVED — `completedRiemannZeta₀` Schwarz from the FE-pair hypothesis.** -/
theorem completedRiemannZeta₀_star
    (h_real : hurwitzEvenFEPair_zero_f_modif_ofReal_target) (s : ℂ) :
    completedRiemannZeta₀ (star s) = star (completedRiemannZeta₀ s) := by
  unfold completedRiemannZeta₀
  exact completedHurwitzZetaEven₀_zero_star h_real s

/-- ⭐ **PROVED — Schwarz reflection for `entireRiemannXi`, modulo the
FE-pair real-lifting hypothesis.** -/
theorem entireRiemannXi_schwarz_of_hurwitzZero
    (h_real : hurwitzEvenFEPair_zero_f_modif_ofReal_target) :
    EntireXi.schwarzReflection := by
  intro s
  unfold entireRiemannXi
  rw [completedRiemannZeta₀_star h_real]
  have h_half : star ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
    rw [Complex.star_def,
        show ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) from by norm_num,
        Complex.conj_ofReal]
  rw [show star ((1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + (1 / 2 : ℂ))
        = (1 / 2 : ℂ) * star s * (star s - 1) * star (completedRiemannZeta₀ s)
          + (1 / 2 : ℂ)
      from by
    rw [star_add, star_mul', star_mul', star_mul', star_sub, star_one, h_half]]

/-- The explicit real-valued witness for the `f_modif` real-lifting
hypothesis: piecewise from `evenKernel 0` on `(1, ∞)` and `(0, 1)`. -/
noncomputable def hurwitzEven_zero_f_modif_real (x : ℝ) : ℝ :=
  (Set.Ioi (1 : ℝ)).indicator (fun y => HurwitzZeta.evenKernel 0 y - 1) x +
  (Set.Ioo (0 : ℝ) 1).indicator
    (fun y => HurwitzZeta.evenKernel 0 y - y ^ (-(1 / 2 : ℝ))) x

/-- ⭐ **PROVED — `hurwitzEvenFEPair 0` has real-valued `f_modif`.** -/
theorem hurwitzEvenFEPair_zero_f_modif_ofReal_holds :
    hurwitzEvenFEPair_zero_f_modif_ofReal_target := by
  refine ⟨hurwitzEven_zero_f_modif_real, ?_⟩
  intro x
  unfold hurwitzEven_zero_f_modif_real WeakFEPair.f_modif
  by_cases h1 : x ∈ Set.Ioi (1 : ℝ)
  · have h2 : x ∉ Set.Ioo (0 : ℝ) 1 :=
      fun hx => absurd hx.2 (not_lt_of_gt h1)
    simp only [Pi.add_apply, Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
               add_zero]
    change ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ)
          - (if (0 : UnitAddCircle) = 0 then 1 else 0)
        = ((HurwitzZeta.evenKernel 0 x - 1 : ℝ) : ℂ)
    rw [if_pos rfl]
    push_cast
    ring
  · by_cases h2 : x ∈ Set.Ioo (0 : ℝ) 1
    · have h1' : x ∉ Set.Ioi (1 : ℝ) := h1
      simp only [Pi.add_apply, Set.indicator_of_notMem h1', Set.indicator_of_mem h2,
                 zero_add]
      change ((HurwitzZeta.evenKernel 0 x : ℝ) : ℂ)
            - ((1 : ℂ) * ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • (1 : ℂ)
          = ((HurwitzZeta.evenKernel 0 x - x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
      rw [one_mul, smul_eq_mul, mul_one]
      push_cast
      ring
    · have h1' : x ∉ Set.Ioi (1 : ℝ) := h1
      simp only [Pi.add_apply, Set.indicator_of_notMem h1', Set.indicator_of_notMem h2,
                 add_zero]
      simp

/-- ⭐ **PROVED — Schwarz reflection for `entireRiemannXi`, unconditional.**
Final discharge of `EntireXi.schwarzReflection` via the FE-pair witness. -/
theorem EntireXi.schwarzReflection_holds :
    EntireXi.schwarzReflection :=
  entireRiemannXi_schwarz_of_hurwitzZero hurwitzEvenFEPair_zero_f_modif_ofReal_holds

end OverflowResidueRH
