/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Topology.Algebra.InfiniteSum.Group
import RiemannHypothesis.HadamardProduct.LogDerivative

/-!
# Multiplicity of occurrence-indexed genus-one products

This module proves that the analytic order of an inverse-square genus-one
product is exactly the cardinality of the corresponding location fiber.
The theorem is independent of any particular completed L-function.
-/

open Set

namespace OverflowResidueRH

/-- A genus-one factor has a simple zero at its designated nonzero location. -/
theorem hadamardGenus1Factor_analyticOrderAt_self
    {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (hadamardGenus1Factor ρ) ρ = 1 := by
  let left : ℂ → ℂ := fun z ↦ 1 - z / ρ
  let right : ℂ → ℂ := fun z ↦ Complex.exp (z / ρ)
  have hleft : AnalyticAt ℂ left ρ := by
    dsimp [left]
    fun_prop
  have hright : AnalyticAt ℂ right ρ := by
    dsimp [right]
    fun_prop
  have hleft_zero : left ρ = 0 := by
    simp [left, hρ]
  have hleft_deriv : deriv left ρ = -(1 / ρ) := by
    dsimp [left]
    simp
  have hleft_order : analyticOrderAt left ρ = 1 :=
    hleft.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hleft_zero (by
      rw [hleft_deriv]
      exact neg_ne_zero.mpr (one_div_ne_zero hρ))
  have hright_order : analyticOrderAt right ρ = 0 :=
    hright.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
  change analyticOrderAt (left * right) ρ = 1
  rw [analyticOrderAt_mul hleft hright, hleft_order, hright_order, add_zero]

/-- A single genus-one factor is entire. -/
theorem hadamardGenus1Factor_differentiable (ρ : ℂ) :
    Differentiable ℂ (hadamardGenus1Factor ρ) :=
  fun z ↦ hadamardGenus1Factor_differentiableAt ρ z

/-- Inverse-square summability and norm properness make the full genus-one
product entire. -/
theorem infiniteHadamardProduct_differentiable_of_invSq_normProper
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) :
    Differentiable ℂ (infiniteHadamardProduct zeroLoc) := by
  let Hex : HadamardFiniteExhaustion zeroLoc :=
    HadamardFiniteExhaustion.of_invSq_mono_exhaustive Hinv
      Hproper.normExhaustion Hproper.normExhaustion_mono
      Hproper.normExhaustion_exhaustive
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc Hex :=
    HadamardProductLocallyUniformLimitData.of_invSq_univ Hinv Hex
      Hproper.normExhaustion_exhaustive
  rw [← differentiableOn_univ]
  exact Hluc.infinite_differentiableOn

/-- Norm properness is inherited by a subtype of the index set. -/
theorem HadamardZeroNormProper.subtype
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) (p : ι → Prop) :
    HadamardZeroNormProper (fun i : Subtype p ↦ zeroLoc i.1) := by
  refine ⟨?_⟩
  intro R
  exact (H.finite_norm_le R).preimage Subtype.val_injective.injOn

/-- Inverse-square Hadamard data is inherited by a subtype when norm
properness supplies the eventual-escape field. -/
theorem HadamardZeroInvSqSummability.subtype_of_normProper
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) (p : ι → Prop) :
    HadamardZeroInvSqSummability (fun i : Subtype p ↦ zeroLoc i.1) :=
  HadamardZeroInvSqSummability.of_invSqSummable_normProper
    (fun i ↦ Hinv.zero_ne i.1)
    (Hinv.inv_sq_summable.subtype p)
    (Hproper.subtype p)

/-- The fiber of a norm-proper location map over one point is finite. -/
theorem HadamardZeroNormProper.finite_fiber
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) (ρ : ℂ) :
    {i : ι | zeroLoc i = ρ}.Finite := by
  apply (H.finite_norm_le ‖ρ‖).subset
  intro i hi
  change ‖zeroLoc i‖ ≤ ‖ρ‖
  rw [hi]

/-- The canonical genus-one product has analytic order equal to the number of
indices located at the point.  Repeated locations are therefore counted with
their full multiplicity. -/
theorem infiniteHadamardProduct_analyticOrderAt_eq_fiber_natCard
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc)
    (ρ : ℂ) :
    analyticOrderAt (infiniteHadamardProduct zeroLoc) ρ =
      (Nat.card {i : ι // zeroLoc i = ρ} : ENat) := by
  classical
  let s : Set ι := {i | zeroLoc i = ρ}
  change analyticOrderAt (infiniteHadamardProduct zeroLoc) ρ =
    (Nat.card s : ENat)
  have hs_finite : s.Finite := Hproper.finite_fiber ρ
  letI : Fintype s := hs_finite.fintype
  let fiberLoc : s → ℂ := fun i ↦ zeroLoc i.1
  let complementLoc : (sᶜ : Set ι) → ℂ := fun i ↦ zeroLoc i.1
  let fiberProduct : ℂ → ℂ := infiniteHadamardProduct fiberLoc
  let complementProduct : ℂ → ℂ := infiniteHadamardProduct complementLoc
  have HcompProper : HadamardZeroNormProper complementLoc :=
    Hproper.subtype (fun i ↦ i ∈ sᶜ)
  have HcompInv : HadamardZeroInvSqSummability complementLoc :=
    Hinv.subtype_of_normProper Hproper (fun i ↦ i ∈ sᶜ)
  have hfiber_eq :
      fiberProduct = fun z ↦ hadamardGenus1Factor ρ z ^ Fintype.card s := by
    funext z
    simp only [fiberProduct, infiniteHadamardProduct, fiberLoc, tprod_fintype]
    calc
      ∏ i : s, hadamardGenus1Factor (zeroLoc i.1) z =
          ∏ _i : s, hadamardGenus1Factor ρ z := by
        apply Fintype.prod_congr
        intro i
        rw [i.2]
      _ = hadamardGenus1Factor ρ z ^ Fintype.card s := by simp
  have hsplit : fiberProduct * complementProduct =
      infiniteHadamardProduct zeroLoc := by
    funext z
    change
      (∏' i : s, hadamardGenus1Factor (zeroLoc i.1) z) *
          (∏' i : (sᶜ : Set ι), hadamardGenus1Factor (zeroLoc i.1) z) =
        ∏' i, hadamardGenus1Factor (zeroLoc i) z
    refine Multipliable.tprod_mul_tprod_compl
      (f := fun i : ι ↦ hadamardGenus1Factor (zeroLoc i) z)
      (s := s) ?_ ?_
    · exact Multipliable.of_finite
    · exact HcompInv.product_multipliable z
  have hfiber_analytic : AnalyticAt ℂ fiberProduct ρ := by
    rw [hfiber_eq]
    exact (hadamardGenus1Factor_differentiable ρ).analyticAt ρ |>.pow _
  have hfiber_order :
      analyticOrderAt fiberProduct ρ = (Fintype.card s : ENat) := by
    rw [hfiber_eq]
    change analyticOrderAt ((hadamardGenus1Factor ρ) ^ Fintype.card s) ρ =
      (Fintype.card s : ENat)
    by_cases hsne : s.Nonempty
    · obtain ⟨i, hi⟩ := hsne
      have hρ : ρ ≠ 0 := by
        rw [← hi]
        exact Hinv.zero_ne i
      rw [analyticOrderAt_pow
        ((hadamardGenus1Factor_differentiable ρ).analyticAt ρ),
        hadamardGenus1Factor_analyticOrderAt_self hρ]
      simp
    · letI : IsEmpty s := ⟨fun i ↦ hsne ⟨i.1, i.2⟩⟩
      have hcard : Fintype.card s = 0 := Fintype.card_eq_zero
      simp [analyticOrderAt_eq_zero]
  have hcomp_diff : Differentiable ℂ complementProduct :=
    infiniteHadamardProduct_differentiable_of_invSq_normProper HcompInv HcompProper
  have hcomp_ne : complementProduct ρ ≠ 0 := by
    apply HcompInv.infiniteProduct_ne_zero
    intro i hi
    exact i.2 hi.symm
  have hcomp_order : analyticOrderAt complementProduct ρ = 0 :=
    (hcomp_diff.analyticAt ρ).analyticOrderAt_eq_zero.mpr hcomp_ne
  rw [← hsplit,
    analyticOrderAt_mul hfiber_analytic (hcomp_diff.analyticAt ρ),
    hfiber_order, hcomp_order, add_zero]
  rw [Nat.card_eq_fintype_card]

/-- Off its indexed zero locations, the logarithmic derivative of the
inverse-square genus-one product is the expected regularized series.  The
singleton restriction removes any need to package a global zero-free region. -/
theorem logDerivativeResponse_infiniteHadamardProduct_eq_tsum_indexed
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc)
    {z : ℂ} (hz : ∀ i : ι, z ≠ zeroLoc i) :
    logDerivativeResponse (infiniteHadamardProduct zeroLoc) z =
      hadamardRegularizedLogDerivSeries zeroLoc z := by
  let Hex : HadamardFiniteExhaustion zeroLoc :=
    HadamardFiniteExhaustion.of_invSq_mono_exhaustive Hinv
      Hproper.normExhaustion Hproper.normExhaustion_mono
      Hproper.normExhaustion_exhaustive
  let HlucSeq : HadamardProductLocallyUniformLimitData zeroLoc Hex :=
    HadamardProductLocallyUniformLimitData.of_invSq_univ Hinv Hex
      Hproper.normExhaustion_exhaustive
  let HderivAll : HadamardFiniteDerivativeLimitData zeroLoc Hex :=
    HadamardFiniteDerivativeLimitData.of_locallyUniformProduct HlucSeq
  let Hderiv : HadamardFiniteDerivativeLimitData zeroLoc Hex :=
    { region := {z}
      derivative_tendsto := by
        intro s hs
        have hsz : s = z := by simpa using hs
        subst s
        exact HderivAll.derivative_tendsto z (mem_univ z) }
  let Hlog : HadamardLogDerivLimitData zeroLoc :=
    HadamardLogDerivLimitData.of_finiteDerivativeLimitData_invSq
      Hinv Hderiv
      (by
        intro s hs
        have hsz : s = z := by simpa [Hderiv] using hs
        subst s
        exact HlucSeq.infinite_differentiableAt (mem_univ z))
      (by
        intro s hs i
        have hsz : s = z := by simpa [Hderiv] using hs
        subst s
        exact hz i)
  apply Hlog.logDeriv_eq_tsum_at z
  change z ∈ ({z} : Set ℂ)
  simp

end OverflowResidueRH
