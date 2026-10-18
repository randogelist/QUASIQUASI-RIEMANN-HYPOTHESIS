/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.ComplexAnalysis.EvenAnalyticOrder
import RiemannHypothesis.HadamardProduct.PairedGenusOne
import RiemannHypothesis.Xi.CanonicalQuotientCriterion

/-!
# Symmetry of the canonical xi product and quotient

The nonzero zeros of the centered xi pullback occur in opposite pairs.
Reindexing the genus-one product by the negation equivalence proves that the
canonical product is even.  The origin factor is even because its analytic
order is even.  Cancellation on a neighborhood where the product is nonzero,
followed by analytic continuation, then proves that the canonical quotient
and its fixed entire logarithm are even as well.
-/

namespace OverflowResidueRH

/-- The multiplicity of the centered xi pullback at the origin is even. -/
theorem entireXiPullbackOriginMultiplicity_even :
    Even entireXiPullbackOriginMultiplicity :=
  analyticOrderNatAt_zero_even_of_even
    (EntireXiPullback_analyticAt 0)
    (entireXiPullback_analyticOrderAt_ne_top 0)
    entireXiPullback_neg

/-- Negating the argument reindexes the nonzero genus-one product by the
zero-negation equivalence. -/
theorem entireXiPullbackInfiniteHadamardProduct_neg (z : ℂ) :
    infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc (-z) =
      infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc z :=
  infiniteHadamardProduct_even_of_neg_equiv
    entireXiPullbackZeroOccurrenceLoc
    entireXiPullbackZeroOccurrenceNegEquiv
    entireXiPullbackZeroOccurrenceNegEquiv_loc z

/-- The full canonical product, including the origin factor, is even. -/
theorem entireXiPullbackCanonicalProduct_neg (z : ℂ) :
    entireXiPullbackCanonicalProduct (-z) =
      entireXiPullbackCanonicalProduct z := by
  unfold entireXiPullbackCanonicalProduct
  change (-z) ^ entireXiPullbackOriginMultiplicity *
      infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc (-z) =
    z ^ entireXiPullbackOriginMultiplicity *
      infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc z
  rw [entireXiPullbackOriginMultiplicity_even.neg_pow,
    entireXiPullbackInfiniteHadamardProduct_neg]

/-- The exponential quotient times the canonical product reconstructs the
centered xi pullback. -/
theorem EntireXiPullback_eq_canonicalQuotient_mul_canonicalProduct
    (H : EntireXiPullbackCanonicalZeroDistribution) (z : ℂ) :
    EntireXiPullback z =
      entireXiPullbackCanonicalQuotient z *
        entireXiPullbackCanonicalProduct z := by
  rw [← exp_entireXiPullbackCanonicalQuotientLog H z]
  exact
    EntireXiPullback_eq_exp_canonicalQuotientLog_mul_canonicalProduct H z

/-- The completed canonical quotient inherits the evenness of xi and of the
canonical product. -/
theorem entireXiPullbackCanonicalQuotient_neg
    (H : EntireXiPullbackCanonicalZeroDistribution) (z : ℂ) :
    entireXiPullbackCanonicalQuotient (-z) =
      entireXiPullbackCanonicalQuotient z := by
  let z₀ : ℂ := Complex.I / 2
  have hz₀_ne : z₀ ≠ 0 := by
    dsimp [z₀]
    exact div_ne_zero Complex.I_ne_zero (by norm_num)
  have hFz₀ : EntireXiPullback z₀ ≠ 0 := by
    rw [show EntireXiPullback z₀ = (1 / 2 : ℂ) by
      simpa only [z₀] using EntireXiPullback_apply_I_div_two]
    norm_num
  have hz₀loc : ∀ i : EntireXiPullbackZeroOccurrence,
      z₀ ≠ entireXiPullbackZeroOccurrenceLoc i := by
    intro i hzi
    apply hFz₀
    rw [hzi]
    exact entireXiPullbackZeroOccurrenceLoc_is_zero i
  have hPz₀ : entireXiPullbackCanonicalProduct z₀ ≠ 0 :=
    entireXiPullbackCanonicalProduct_ne_zero_of_away H hz₀_ne hz₀loc
  have hPevent : ∀ᶠ w in nhds z₀,
      entireXiPullbackCanonicalProduct w ≠ 0 :=
    ((entireXiPullbackCanonicalProduct_differentiable H) z₀).continuousAt
      |>.eventually_ne hPz₀
  have hqevent :
      (fun w : ℂ ↦ entireXiPullbackCanonicalQuotient (-w)) =ᶠ[nhds z₀]
        entireXiPullbackCanonicalQuotient := by
    filter_upwards [hPevent] with w hPw
    have hneg :=
      EntireXiPullback_eq_canonicalQuotient_mul_canonicalProduct H (-w)
    have hpos :=
      EntireXiPullback_eq_canonicalQuotient_mul_canonicalProduct H w
    rw [entireXiPullback_neg,
      entireXiPullbackCanonicalProduct_neg] at hneg
    exact mul_right_cancel₀ hPw (hneg.symm.trans hpos)
  have hq : Differentiable ℂ entireXiPullbackCanonicalQuotient :=
    entireXiPullbackCanonicalQuotient_differentiable H
  have hqneg : Differentiable ℂ
      (fun w : ℂ ↦ entireXiPullbackCanonicalQuotient (-w)) := by
    fun_prop
  have hfun : (fun w : ℂ ↦ entireXiPullbackCanonicalQuotient (-w)) =
      entireXiPullbackCanonicalQuotient := by
    apply AnalyticOnNhd.eq_of_eventuallyEq
      (DifferentiableOn.analyticOnNhd hqneg.differentiableOn isOpen_univ)
      (DifferentiableOn.analyticOnNhd hq.differentiableOn isOpen_univ)
      hqevent
  exact congrFun hfun z

/-- The chosen global entire logarithm of the canonical quotient is even,
not merely even modulo an integral multiple of `2πi`. -/
theorem entireXiPullbackCanonicalQuotientLog_neg
    (H : EntireXiPullbackCanonicalZeroDistribution) (z : ℂ) :
    entireXiPullbackCanonicalQuotientLog H (-z) =
      entireXiPullbackCanonicalQuotientLog H z := by
  let h : ℂ → ℂ := entireXiPullbackCanonicalQuotientLog H
  obtain ⟨c, hc⟩ := differentiable_logs_eq_add_const
    (entireXiPullbackCanonicalQuotientLog_differentiable H)
    (show Differentiable ℂ (fun w : ℂ ↦ h (-w)) by
      simpa [h, Function.comp_def] using
        (entireXiPullbackCanonicalQuotientLog_differentiable H).comp
          differentiable_neg)
    (fun w ↦ by
      dsimp [h]
      rw [exp_entireXiPullbackCanonicalQuotientLog H (-w),
        exp_entireXiPullbackCanonicalQuotientLog H w,
        entireXiPullbackCanonicalQuotient_neg H w])
  have hc0 := hc 0
  have hc_zero : c = 0 := by
    dsimp [h] at hc0
    simp only [neg_zero] at hc0
    linear_combination -hc0
  have hz := hc z
  dsimp [h] at hz ⊢
  simpa [hc_zero] using hz

end OverflowResidueRH
