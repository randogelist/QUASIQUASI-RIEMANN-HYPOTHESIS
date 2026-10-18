/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Vanishing order of an even analytic function

An analytic function invariant under `z ↦ -z` has even finite vanishing
order at the origin.  This small local lemma is useful when a symmetric
Hadamard divisor contains a separately recorded origin factor.
-/

namespace OverflowResidueRH

/-- The finite analytic order at the origin of an even complex analytic
function is even. -/
theorem analyticOrderNatAt_zero_even_of_even
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hfinite : analyticOrderAt f 0 ≠ ⊤)
    (heven : ∀ z : ℂ, f (-z) = f z) :
    Even (analyticOrderNatAt f 0) := by
  let n : ℕ := analyticOrderNatAt f 0
  have horder : analyticOrderAt f 0 = (n : ENat) := by
    exact (Nat.cast_analyticOrderNatAt hfinite).symm
  have hnth_ne : iteratedDeriv n f 0 ≠ 0 :=
    ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp horder).2
  by_contra hneven
  have hnodd : Odd n := Nat.not_even_iff_odd.mp hneven
  have hfun : (fun z : ℂ ↦ f (-z)) = f := funext heven
  have hiter := congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv n g 0) hfun
  rw [iteratedDeriv_comp_neg, neg_zero, hnodd.neg_one_pow] at hiter
  have hnth_zero : iteratedDeriv n f 0 = 0 := by
    have hneg : -(iteratedDeriv n f 0) = iteratedDeriv n f 0 := by
      simpa [smul_eq_mul] using hiter
    have htwo : (2 : ℂ) * iteratedDeriv n f 0 = 0 := by
      linear_combination -hneg
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  exact hnth_ne hnth_zero

end OverflowResidueRH
