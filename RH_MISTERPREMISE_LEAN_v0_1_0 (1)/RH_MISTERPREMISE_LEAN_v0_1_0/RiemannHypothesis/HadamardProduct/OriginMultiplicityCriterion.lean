/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Cardinality
import RiemannHypothesis.HadamardProduct.StrictRealZeroCriterion

/-!
# Affine genus-one products with a zero at the origin

This module extends the affine genus-one product by a factor `z ^ m`.  It
allows a canonical-product interface to record a zero of arbitrary finite
multiplicity at the origin instead of silently forcing the represented entire
function to be nonzero there.
-/

namespace OverflowResidueRH

open Filter Topology

/-- An affine-exponential genus-one product with an additional origin factor
`z ^ m`. -/
noncomputable def expAffineGenusOneProductWithOriginMultiplicity
    (m : ℕ) (C a b : ℂ) (zeroLoc : ℕ → ℂ) : ℂ → ℂ :=
  fun z => z ^ m * expAffineGenusOneProduct C a b zeroLoc z

/-- With a nonzero affine prefactor, the explicit origin exponent is exactly
the analytic order of the product at the origin. -/
theorem expAffineGenusOneProductWithOriginMultiplicity_analyticOrderAt_zero
    (m : ℕ) {C a b : ℂ} (hC : C ≠ 0)
    (zeroLoc : ℕ → ℂ) (H : NatHadamardZeroInvSqData zeroLoc) :
    analyticOrderAt
      (expAffineGenusOneProductWithOriginMultiplicity m C a b zeroLoc) 0 =
        (m : ℕ∞) := by
  let Hgen : HadamardZeroInvSqSummability zeroLoc :=
    H.toHadamardZeroInvSqSummability
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion Hgen) :=
    natHadamardProductLocallyUniformLimitData Hgen
  have hbase_differentiable :
      Differentiable ℂ (expAffineGenusOneProduct C a b zeroLoc) := by
    intro z
    unfold expAffineGenusOneProduct
    exact ((by fun_prop :
      DifferentiableAt ℂ
        (fun w : ℂ => C * Complex.exp (a + b * w)) z).mul
          (Hluc.infinite_differentiableAt (Set.mem_univ z)))
  have hbase_analytic :
      AnalyticAt ℂ (expAffineGenusOneProduct C a b zeroLoc) 0 :=
    hbase_differentiable.analyticAt 0
  have hbase_ne :
      expAffineGenusOneProduct C a b zeroLoc 0 ≠ 0 := by
    unfold expAffineGenusOneProduct
    exact mul_ne_zero
      (mul_ne_zero hC (Complex.exp_ne_zero _))
      (Hgen.infiniteProduct_ne_zero (fun i => (H.zero_ne i).symm))
  have hfull_differentiable :
      Differentiable ℂ
        (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc) := by
    intro z
    unfold expAffineGenusOneProductWithOriginMultiplicity
    exact (by fun_prop :
      DifferentiableAt ℂ (fun w : ℂ => w ^ m) z).mul
        (hbase_differentiable z)
  have hfull_analytic :
      AnalyticAt ℂ
        (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc) 0 :=
    hfull_differentiable.analyticAt 0
  rw [hfull_analytic.analyticOrderAt_eq_natCast]
  refine ⟨expAffineGenusOneProduct C a b zeroLoc,
    hbase_analytic, hbase_ne, ?_⟩
  filter_upwards with z
  simp [expAffineGenusOneProductWithOriginMultiplicity]

/-- The logarithmic derivative of the origin factor `z ^ m`.  This identity
uses Lean's totalized division and therefore also holds at `z = 0`; the main
product identity below is stated away from zero for its mathematical use. -/
theorem logDerivativeResponse_pow_id (m : ℕ) (z : ℂ) :
    logDerivativeResponse (fun w : ℂ => w ^ m) z = (m : ℂ) / z := by
  rw [logDerivativeResponse_eq_logDeriv]
  exact logDeriv_pow z m

/-- Away from the origin and the indexed zeros, the logarithmic derivative is
the origin contribution `m / z`, plus the affine slope, plus the regularized
zero-product response. -/
theorem logDerivativeResponse_expAffineGenusOneProductWithOriginMultiplicity
    {m : ℕ} {C a b : ℂ} (hC : C ≠ 0)
    {zeroLoc : ℕ → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc)
    {z : ℂ} (hz0 : z ≠ 0) (hz : ∀ i : ℕ, z ≠ zeroLoc i) :
    logDerivativeResponse
        (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc) z =
      (m : ℂ) / z + b +
        logDerivativeResponse (infiniteHadamardProduct zeroLoc) z := by
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion H) :=
    natHadamardProductLocallyUniformLimitData H
  have hpow_diff :
      DifferentiableAt ℂ (fun w : ℂ => w ^ m) z := by fun_prop
  have hbase_diff :
      DifferentiableAt ℂ (expAffineGenusOneProduct C a b zeroLoc) z := by
    unfold expAffineGenusOneProduct
    exact (by fun_prop :
      DifferentiableAt ℂ (fun w : ℂ => C * Complex.exp (a + b * w)) z).mul
        (Hluc.infinite_differentiableAt (Set.mem_univ z))
  have hbase_ne : expAffineGenusOneProduct C a b zeroLoc z ≠ 0 := by
    unfold expAffineGenusOneProduct
    exact mul_ne_zero
      (mul_ne_zero hC (Complex.exp_ne_zero _))
      (H.infiniteProduct_ne_zero hz)
  unfold expAffineGenusOneProductWithOriginMultiplicity
  rw [logDerivativeResponse_mul_eq_add
      hpow_diff hbase_diff (pow_ne_zero m hz0) hbase_ne,
    logDerivativeResponse_pow_id,
    logDerivativeResponse_expAffineGenusOneProduct hC H hz]
  ring

/-- A countable zero sequence cannot cover the complex plane, even after the
origin is added.  This supplies a nonzero point for the global identity
theorem when the represented function itself vanishes at the origin. -/
private theorem exists_point_away_from_origin_and_zero_sequence
    (zeroLoc : ℕ → ℂ) :
    ∃ z : ℂ, z ≠ 0 ∧ ∀ i : ℕ, z ≠ zeroLoc i := by
  let S : Set ℂ := Set.range zeroLoc ∪ {0}
  have hS_countable : S.Countable :=
    (Set.countable_range zeroLoc).union (Set.countable_singleton 0)
  have hS_ne_univ : S ≠ Set.univ := by
    intro hS
    apply not_countable_complex
    rw [← hS]
    exact hS_countable
  have hexists : ∃ z : ℂ, z ∉ S := by
    by_contra h
    apply hS_ne_univ
    apply Set.eq_univ_of_forall
    intro z
    by_contra hz
    exact h ⟨z, hz⟩
  obtain ⟨z, hz⟩ := hexists
  refine ⟨z, ?_, ?_⟩
  · intro hz0
    apply hz
    right
    simp [hz0]
  · intro i hzi
    apply hz
    left
    exact ⟨i, hzi.symm⟩

/-- The origin contribution `m / z` has nonpositive imaginary part in the
open upper half-plane. -/
private theorem originMultiplicityResponse_im_nonpos
    (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    (((m : ℂ) / z).im) ≤ 0 := by
  rw [Complex.div_im]
  have hm_im : ((m : ℂ).im) = 0 := by simp
  have hm_re : ((m : ℂ).re) = (m : ℝ) := by simp
  rw [hm_im, hm_re]
  simp only [zero_mul, zero_div, zero_sub]
  exact neg_nonpos.mpr <| div_nonneg
    (mul_nonneg (Nat.cast_nonneg m) (le_of_lt hz))
    (Complex.normSq_nonneg z)

/-- Schwarz reflection of the product with an origin factor implies Schwarz
reflection of the underlying affine genus-one product.  Away from the origin
this is cancellation of `(star z) ^ m`; continuity fills the puncture. -/
private theorem expAffineGenusOneProduct_schwarz_of_withOriginMultiplicity_schwarz
    (m : ℕ) {C a b : ℂ} (zeroLoc : ℕ → ℂ)
    (H : NatHadamardZeroInvSqData zeroLoc)
    (h_schwarz : ∀ z : ℂ,
      expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc (star z) =
        star (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc z)) :
    ∀ z : ℂ,
      expAffineGenusOneProduct C a b zeroLoc (star z) =
        star (expAffineGenusOneProduct C a b zeroLoc z) := by
  let Hgen : HadamardZeroInvSqSummability zeroLoc :=
    H.toHadamardZeroInvSqSummability
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion Hgen) :=
    natHadamardProductLocallyUniformLimitData Hgen
  have hbase_continuous :
      Continuous (expAffineGenusOneProduct C a b zeroLoc) := by
    refine continuous_iff_continuousAt.mpr (fun z => ?_)
    unfold expAffineGenusOneProduct
    exact ((by fun_prop :
        DifferentiableAt ℂ
          (fun w : ℂ => C * Complex.exp (a + b * w)) z).mul
            (Hluc.infinite_differentiableAt (Set.mem_univ z))).continuousAt
  have hpunctured : ∀ z : ℂ, z ≠ 0 →
      expAffineGenusOneProduct C a b zeroLoc (star z) =
        star (expAffineGenusOneProduct C a b zeroLoc z) := by
    intro z hz
    have hfull := h_schwarz z
    unfold expAffineGenusOneProductWithOriginMultiplicity at hfull
    simp only [star_mul', star_pow] at hfull
    exact mul_left_cancel₀ (pow_ne_zero m (star_ne_zero.mpr hz)) hfull
  intro z
  by_cases hz : z = 0
  · subst z
    have hleft :
        Tendsto
          (fun w : ℂ =>
            expAffineGenusOneProduct C a b zeroLoc (star w))
          (𝓝[≠] 0)
          (𝓝 (expAffineGenusOneProduct C a b zeroLoc (star 0))) :=
      (hbase_continuous.comp continuous_star).continuousAt.mono_left inf_le_left
    have hright :
        Tendsto
          (fun w : ℂ =>
            star (expAffineGenusOneProduct C a b zeroLoc w))
          (𝓝[≠] 0)
          (𝓝 (star (expAffineGenusOneProduct C a b zeroLoc 0))) :=
      (continuous_star.comp hbase_continuous).continuousAt.mono_left inf_le_left
    have heq :
        (fun w : ℂ =>
          expAffineGenusOneProduct C a b zeroLoc (star w)) =ᶠ[𝓝[≠] 0]
        (fun w : ℂ =>
          star (expAffineGenusOneProduct C a b zeroLoc w)) := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      exact hpunctured w (by simpa using hw)
    simpa using tendsto_nhds_unique_of_eventuallyEq hleft hright heq
  · exact hpunctured z hz

/-- Schwarz reflection still forces the affine slope to be real when a finite
zero of arbitrary multiplicity is placed at the origin. -/
theorem expAffineGenusOneProductWithOriginMultiplicity_slope_real_of_schwarz
    (m : ℕ) {C a b : ℂ} (hC : C ≠ 0)
    (zeroLoc : ℕ → ℂ) (H : NatHadamardZeroInvSqData zeroLoc)
    (h_schwarz : ∀ z : ℂ,
      expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc (star z) =
        star (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc z)) :
    b.im = 0 :=
  expAffineGenusOneProduct_slope_real_of_schwarz hC zeroLoc H
    (expAffineGenusOneProduct_schwarz_of_withOriginMultiplicity_schwarz
      m zeroLoc H h_schwarz)

/-- **Exact affine genus-one criterion with origin multiplicity.**  Under
minimal natural-number-indexed inverse-square data, a nonzero affine
prefactor, real affine slope, and Schwarz reflection, strict anti-Herglotz
behavior is equivalent to every zero of the full function being real.

Unlike `expAffineGenusOneProduct_strictAntiHerglotz_iff_zeros_real`, this
statement permits an arbitrary finite-order zero at the origin. -/
theorem
    expAffineGenusOneProductWithOriginMultiplicity_strictAntiHerglotz_iff_zeros_real
    (m : ℕ) {C a b : ℂ} (hC : C ≠ 0) (hb : b.im = 0)
    (zeroLoc : ℕ → ℂ)
    (H : NatHadamardZeroInvSqData zeroLoc)
    (h_schwarz : ∀ z : ℂ,
      expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc (star z) =
        star (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc z)) :
    StrictAntiHerglotzUHP
        (logDerivativeResponse
          (expAffineGenusOneProductWithOriginMultiplicity
            m C a b zeroLoc)) ↔
      ∀ rho : ℂ,
        expAffineGenusOneProductWithOriginMultiplicity
            m C a b zeroLoc rho = 0 →
          rho.im = 0 := by
  let Hgen : HadamardZeroInvSqSummability zeroLoc :=
    H.toHadamardZeroInvSqSummability
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion Hgen) :=
    natHadamardProductLocallyUniformLimitData Hgen
  have hdifferentiable :
      Differentiable ℂ
        (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc) := by
    intro z
    unfold expAffineGenusOneProductWithOriginMultiplicity
    apply DifferentiableAt.mul
    · fun_prop
    · unfold expAffineGenusOneProduct
      exact (by fun_prop :
        DifferentiableAt ℂ
          (fun w : ℂ => C * Complex.exp (a + b * w)) z).mul
            (Hluc.infinite_differentiableAt (Set.mem_univ z))
  have hanalytic :
      AnalyticOnNhd ℂ
        (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc) Set.univ :=
    fun z _hz => hdifferentiable.analyticAt z
  have hnontrivial :
      ∃ z : ℂ,
        expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc z ≠ 0 := by
    obtain ⟨z, hz0, hz⟩ :=
      exists_point_away_from_origin_and_zero_sequence zeroLoc
    refine ⟨z, ?_⟩
    unfold expAffineGenusOneProductWithOriginMultiplicity
    apply mul_ne_zero (pow_ne_zero m hz0)
    unfold expAffineGenusOneProduct
    exact mul_ne_zero
      (mul_ne_zero hC (Complex.exp_ne_zero _))
      (Hgen.infiniteProduct_ne_zero hz)
  constructor
  · intro hstrict
    exact entire_function_roots_real_of_analytic_nontrivial
      (expAffineGenusOneProductWithOriginMultiplicity m C a b zeroLoc)
      hanalytic hnontrivial
      (fun z hz _hz_nonzero => hstrict.antiHerglotz z hz)
      h_schwarz
  · intro hzeros
    have hreal : ∀ i : ℕ, (zeroLoc i).im = 0 := by
      intro i
      apply hzeros (zeroLoc i)
      unfold expAffineGenusOneProductWithOriginMultiplicity
      unfold expAffineGenusOneProduct
      rw [infiniteHadamardProduct_eq_zero_at_zeroLoc H.zero_ne i]
      simp
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      rw [hzero, Complex.zero_im] at hz
      linarith
    have hz_ne : ∀ i : ℕ, z ≠ zeroLoc i := by
      intro i hzi
      have him := congrArg Complex.im hzi
      rw [hreal i] at him
      linarith
    rw [logDerivativeResponse_expAffineGenusOneProductWithOriginMultiplicity
      hC Hgen hz0 hz_ne]
    rw [Complex.add_im, Complex.add_im, hb, add_zero]
    have horigin := originMultiplicityResponse_im_nonpos m z hz
    have hproduct :=
      infiniteHadamardProduct_strictAntiHerglotz_of_nat_invSqData
        zeroLoc H hreal z hz
    linarith

/-- **Slope-free exact criterion with origin multiplicity.**  Schwarz
reflection determines the affine slope, so an independent reality hypothesis
on `b` is unnecessary. -/
theorem
    expAffineGenusOneProductWithOriginMultiplicity_strictAntiHerglotz_iff_zeros_real_of_schwarz
    (m : ℕ) {C a b : ℂ} (hC : C ≠ 0)
    (zeroLoc : ℕ → ℂ)
    (H : NatHadamardZeroInvSqData zeroLoc)
    (h_schwarz : ∀ z : ℂ,
      expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc (star z) =
        star (expAffineGenusOneProductWithOriginMultiplicity
          m C a b zeroLoc z)) :
    StrictAntiHerglotzUHP
        (logDerivativeResponse
          (expAffineGenusOneProductWithOriginMultiplicity
            m C a b zeroLoc)) ↔
      ∀ rho : ℂ,
        expAffineGenusOneProductWithOriginMultiplicity
            m C a b zeroLoc rho = 0 →
          rho.im = 0 :=
  expAffineGenusOneProductWithOriginMultiplicity_strictAntiHerglotz_iff_zeros_real
    m hC
    (expAffineGenusOneProductWithOriginMultiplicity_slope_real_of_schwarz
      m hC zeroLoc H h_schwarz)
    zeroLoc H h_schwarz

end OverflowResidueRH
