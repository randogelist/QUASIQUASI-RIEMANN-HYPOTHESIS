/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.CanonicalProductDivisor
import RiemannHypothesis.Xi.CanonicalDivisor

/-!
# Canonical-product multiplicity for the centered xi pullback

This module specializes the generic occurrence-indexed divisor theorem to the
canonical nonzero zero occurrences of `EntireXiPullback`, including its
separately recorded origin multiplicity.
-/

open Set

namespace OverflowResidueRH

/-- The location fiber over a canonical nonzero zero is the same type as the
fiber of the occurrence projection over that zero. -/
noncomputable def entireXiPullbackZeroOccurrenceLocFiberEquiv
    (z : EntireXiPullbackNonzeroZero) :
    {i : EntireXiPullbackZeroOccurrence //
        entireXiPullbackZeroOccurrenceLoc i = z.1} ≃
      {i : EntireXiPullbackZeroOccurrence // i.1 = z} where
  toFun i := ⟨i.1, Subtype.ext i.2⟩
  invFun i := ⟨i.1, congrArg Subtype.val i.2⟩
  left_inv _i := Subtype.ext rfl
  right_inv _i := Subtype.ext rfl

/-- Away from the origin, the location-fiber cardinality of the canonical xi
divisor is exactly the analytic multiplicity of the pullback. -/
theorem entireXiPullbackZeroOccurrenceLoc_fiber_natCard
    {z : ℂ} (hz0 : z ≠ 0) :
    Nat.card {i : EntireXiPullbackZeroOccurrence //
        entireXiPullbackZeroOccurrenceLoc i = z} =
      analyticOrderNatAt EntireXiPullback z := by
  by_cases hz : EntireXiPullback z = 0
  · let ρ : EntireXiPullbackNonzeroZero := ⟨z, hz, hz0⟩
    calc
      Nat.card {i : EntireXiPullbackZeroOccurrence //
          entireXiPullbackZeroOccurrenceLoc i = z} =
          Nat.card {i : EntireXiPullbackZeroOccurrence // i.1 = ρ} := by
        exact Nat.card_congr
          (entireXiPullbackZeroOccurrenceLocFiberEquiv ρ)
      _ = analyticOrderNatAt EntireXiPullback z := by
        simpa [ρ] using entireXiPullbackZeroOccurrence_fiber_natCard ρ
  · letI : IsEmpty {i : EntireXiPullbackZeroOccurrence //
        entireXiPullbackZeroOccurrenceLoc i = z} :=
      ⟨fun i ↦ hz (by
        rw [← i.2]
        exact entireXiPullbackZeroOccurrenceLoc_is_zero i.1)⟩
    have horder : analyticOrderAt EntireXiPullback z = 0 :=
      (EntireXiPullback_analyticAt z).analyticOrderAt_eq_zero.mpr hz
    simp [analyticOrderNatAt, horder]

/-- The finite origin factor times the occurrence-indexed genus-one product. -/
noncomputable def entireXiPullbackCanonicalProduct : ℂ → ℂ :=
  (fun z ↦ z ^ entireXiPullbackOriginMultiplicity) *
    infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc

/-- The canonical xi product is entire under the sole global inverse-square
zero-distribution hypothesis. -/
theorem entireXiPullbackCanonicalProduct_differentiable
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    Differentiable ℂ entireXiPullbackCanonicalProduct := by
  have hmonomial : Differentiable ℂ
      (fun z : ℂ ↦ z ^ entireXiPullbackOriginMultiplicity) := by
    fun_prop
  have hproduct : Differentiable ℂ
      (infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc) :=
    infiniteHadamardProduct_differentiable_of_invSq_normProper
      H.toHadamardZeroInvSqSummability
      entireXiPullbackZeroOccurrenceNormProper
  exact hmonomial.mul hproduct

/-- The order of the origin monomial at the origin is its exponent. -/
theorem analyticOrderAt_monomial_zero (m : ℕ) :
    analyticOrderAt (fun z : ℂ ↦ z ^ m) 0 = (m : ENat) := by
  change analyticOrderAt ((id : ℂ → ℂ) ^ m) (0 : ℂ) = (m : ENat)
  rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp

/-- The canonical product and `EntireXiPullback` have the same analytic order
at every point. -/
theorem entireXiPullbackCanonicalProduct_analyticOrderAt
    (H : EntireXiPullbackCanonicalZeroDistribution) (z : ℂ) :
    analyticOrderAt entireXiPullbackCanonicalProduct z =
      analyticOrderAt EntireXiPullback z := by
  let Hinv : HadamardZeroInvSqSummability
      entireXiPullbackZeroOccurrenceLoc :=
    H.toHadamardZeroInvSqSummability
  have hmonomial : AnalyticAt ℂ
      (fun w : ℂ ↦ w ^ entireXiPullbackOriginMultiplicity) z := by
    fun_prop
  have hproduct : AnalyticAt ℂ
      (infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc) z :=
    (infiniteHadamardProduct_differentiable_of_invSq_normProper
      Hinv entireXiPullbackZeroOccurrenceNormProper).analyticAt z
  change analyticOrderAt
      ((fun w : ℂ ↦ w ^ entireXiPullbackOriginMultiplicity) *
        infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc) z =
    analyticOrderAt EntireXiPullback z
  rw [analyticOrderAt_mul hmonomial hproduct,
    infiniteHadamardProduct_analyticOrderAt_eq_fiber_natCard
      Hinv entireXiPullbackZeroOccurrenceNormProper z]
  by_cases hz0 : z = 0
  · subst z
    letI : IsEmpty {i : EntireXiPullbackZeroOccurrence //
        entireXiPullbackZeroOccurrenceLoc i = 0} :=
      ⟨fun i ↦ entireXiPullbackZeroOccurrenceLoc_ne_zero i.1 i.2⟩
    rw [Nat.card_of_isEmpty]
    simp only [ENat.coe_zero, add_zero]
    rw [analyticOrderAt_monomial_zero,
      entireXiPullback_analyticOrderAt_zero]
  · rw [hmonomial.analyticOrderAt_eq_zero.mpr
        (pow_ne_zero entireXiPullbackOriginMultiplicity hz0),
      zero_add,
      entireXiPullbackZeroOccurrenceLoc_fiber_natCard hz0,
      Nat.cast_analyticOrderNatAt
        (entireXiPullback_analyticOrderAt_ne_top z)]

end OverflowResidueRH
