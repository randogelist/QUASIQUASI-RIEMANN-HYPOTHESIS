/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.CanonicalProductDivisor
import RiemannHypothesis.HadamardProduct.CanonicalProductGrowth
import RiemannHypothesis.HadamardProduct.DyadicZeroCount
import RiemannHypothesis.HadamardProduct.IndexedRealZeroSign
import RiemannHypothesis.RealZeros.EntireFunctions

/-!
# A reusable completed-L-function Hadamard criterion

This module packages the analytic skeleton shared by completed L-functions in
critical-line coordinates.  The function is entire, even, and Schwarz
reflecting.  Its nonzero divisor is indexed by occurrences, so repeated
locations encode exact multiplicity.  A cumulative dyadic `O(R log R)` count
supplies inverse-square summability, which in turn gives an entire canonical
product of minimal quadratic type.

The final theorem identifies the assertion that every zero is real with a
strict anti-Herglotz sign for the logarithmic derivative.  It uses no xi,
zeta, theta-kernel, or arithmetic definitions.
-/

open Filter Metric Real Set Topology

namespace OverflowResidueRH

universe u

/-- The origin monomial times an occurrence-indexed genus-one product. -/
noncomputable def canonicalProductWithOrigin
    (m : ℕ) {ι : Type*} (zeroLoc : ι → ℂ) : ℂ → ℂ :=
  (fun z ↦ z ^ m) * infiniteHadamardProduct zeroLoc

/-- Inverse-square summability and norm properness make the canonical product
with an origin factor entire. -/
theorem canonicalProductWithOrigin_differentiable
    {ι : Type*} {zeroLoc : ι → ℂ} (m : ℕ)
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) :
    Differentiable ℂ (canonicalProductWithOrigin m zeroLoc) := by
  unfold canonicalProductWithOrigin
  exact (show Differentiable ℂ (fun z : ℂ ↦ z ^ m) by fun_prop).mul
    (infiniteHadamardProduct_differentiable_of_invSq_normProper
      Hinv Hproper)

/-- The analytic divisor of the canonical product is the origin multiplicity
plus the cardinality of each nonzero location fiber. -/
theorem canonicalProductWithOrigin_analyticOrderAt
    {ι : Type*} {zeroLoc : ι → ℂ} (m : ℕ)
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) (z : ℂ) :
    analyticOrderAt (canonicalProductWithOrigin m zeroLoc) z =
      if z = 0 then (m : ENat)
      else (Nat.card {i : ι // zeroLoc i = z} : ENat) := by
  have hmonomial : AnalyticAt ℂ (fun w : ℂ ↦ w ^ m) z := by fun_prop
  have hproduct : AnalyticAt ℂ (infiniteHadamardProduct zeroLoc) z :=
    (infiniteHadamardProduct_differentiable_of_invSq_normProper
      Hinv Hproper).analyticAt z
  unfold canonicalProductWithOrigin
  rw [analyticOrderAt_mul hmonomial hproduct,
    infiniteHadamardProduct_analyticOrderAt_eq_fiber_natCard
      Hinv Hproper z]
  by_cases hz : z = 0
  · subst z
    letI : IsEmpty {i : ι // zeroLoc i = 0} :=
      ⟨fun i ↦ Hinv.zero_ne i.1 i.2⟩
    rw [Nat.card_of_isEmpty]
    simp only [ENat.coe_zero, add_zero, if_pos]
    change analyticOrderAt ((id : ℂ → ℂ) ^ m) (0 : ℂ) = (m : ENat)
    rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
    simp
  · rw [hmonomial.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hz),
      zero_add, if_neg hz]

/-- The canonical product has logarithmic maximum modulus `o(‖z‖²)`. -/
theorem canonicalProductWithOrigin_hasSubquadraticLogNormGrowthAtInfinity
    {ι : Type*} {zeroLoc : ι → ℂ} (m : ℕ)
    (Hinv : HadamardZeroInvSqSummability zeroLoc) :
    HasSubquadraticLogNormGrowthAtInfinity
      (canonicalProductWithOrigin m zeroLoc) := by
  unfold canonicalProductWithOrigin
  exact (monomial_hasSubquadraticLogNormGrowthAtInfinity m).mul
    (infiniteHadamardProduct_hasSubquadraticLogNormGrowthAtInfinity Hinv)

/-- For an entire canonical product, minimal logarithmic type is equivalent
to a subquadratic Nevanlinna characteristic bound. -/
theorem canonicalProductWithOrigin_hasSubquadraticCharacteristicGrowthAtInfinity
    {ι : Type*} {zeroLoc : ι → ℂ} (m : ℕ)
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) :
    HasSubquadraticCharacteristicGrowthAtInfinity
      (canonicalProductWithOrigin m zeroLoc) := by
  have hdiff := canonicalProductWithOrigin_differentiable m Hinv Hproper
  exact (canonicalProductWithOrigin_hasSubquadraticLogNormGrowthAtInfinity
      m Hinv).toProximityGrowthAtInfinity hdiff.continuous
    |>.toCharacteristicGrowthAtInfinity_of_analytic
      (DifferentiableOn.analyticOnNhd hdiff.differentiableOn isOpen_univ)

/-- The derivative of an even entire function is odd. -/
theorem deriv_neg_of_even
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (heven : ∀ z : ℂ, F (-z) = F z) (z : ℂ) :
    deriv F (-z) = -deriv F z := by
  have hinner : HasDerivAt (fun w : ℂ ↦ -w) (-1) z :=
    (hasDerivAt_id z).neg
  have houter : HasDerivAt F (deriv F (-z)) (-z) :=
    (hF (-z)).hasDerivAt
  have hcomp : HasDerivAt (fun w : ℂ ↦ F (-w))
      (deriv F (-z) * (-1)) z := by
    simpa [Function.comp_def] using houter.comp z hinner
  have hfun : (fun w : ℂ ↦ F (-w)) = F := funext heven
  have hderiv_fun := congrArg (fun f : ℂ → ℂ ↦ deriv f z) hfun
  have hderiv : deriv F z = deriv F (-z) * (-1) := by
    rw [← hderiv_fun]
    exact hcomp.deriv
  have hneg := congrArg Neg.neg hderiv
  simpa using hneg.symm

/-- The totalized logarithmic derivative of an even entire function is odd. -/
theorem logDerivativeResponse_neg_of_even
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (heven : ∀ z : ℂ, F (-z) = F z) (z : ℂ) :
    logDerivativeResponse F (-z) = -logDerivativeResponse F z := by
  unfold logDerivativeResponse
  rw [deriv_neg_of_even hF heven, heven]
  ring

/-- `F` has only real zeros. -/
def HasOnlyRealZeros (F : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F z = 0 → z.im = 0

/-- Complete analytic and divisor data for a completed L-function in centered
critical-line coordinates.  The dyadic count is the quantitative source of
inverse-square summability; `analyticOrderAt_eq` records exact multiplicity. -/
structure CompletedLFunctionHadamardData
    (F : ℂ → ℂ) (ι : Type u) : Type (u + 1) where
  analytic : AnalyticOnNhd ℂ F univ
  nontrivial : ∃ z : ℂ, F z ≠ 0
  even : ∀ z : ℂ, F (-z) = F z
  schwarz : ∀ z : ℂ, F (star z) = star (F z)
  originMultiplicity : ℕ
  zeroLoc : ι → ℂ
  dyadicZeros : HadamardZeroDyadicCumulativeCountData zeroLoc
  zeroLoc_is_zero : ∀ i : ι, F (zeroLoc i) = 0
  analyticOrderAt_eq : ∀ z : ℂ,
    analyticOrderAt F z =
      if z = 0 then (originMultiplicity : ENat)
      else (Nat.card {i : ι // zeroLoc i = z} : ENat)
  b : ℂ
  b_im : b.im = 0
  logDerivative_expansion :
    ∀ z : ℂ, z ≠ 0 → (∀ i : ι, z ≠ zeroLoc i) →
      logDerivativeResponse F z =
        (originMultiplicity : ℂ) / z + b +
          hadamardRegularizedLogDerivSeries zeroLoc z
  support_nonempty : originMultiplicity ≠ 0 ∨ Nonempty ι

/-- The inverse-square divisor package derived from the dyadic count. -/
def CompletedLFunctionHadamardData.zeroData
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι) :
    HadamardZeroInvSqSummability H.zeroLoc :=
  H.dyadicZeros.toHadamardZeroInvSqSummability

/-- The canonical product attached to the occurrence-indexed divisor. -/
noncomputable def CompletedLFunctionHadamardData.canonicalProduct
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι) : ℂ → ℂ :=
  canonicalProductWithOrigin H.originMultiplicity H.zeroLoc

theorem CompletedLFunctionHadamardData.canonicalProduct_differentiable
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι) :
    Differentiable ℂ H.canonicalProduct :=
  canonicalProductWithOrigin_differentiable H.originMultiplicity H.zeroData
    H.dyadicZeros.normProper

/-- The constructed canonical product has exactly the analytic divisor of
the completed L-function. -/
theorem CompletedLFunctionHadamardData.canonicalProduct_analyticOrderAt
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι) (z : ℂ) :
    analyticOrderAt H.canonicalProduct z = analyticOrderAt F z := by
  change analyticOrderAt
    (canonicalProductWithOrigin H.originMultiplicity H.zeroLoc) z =
      analyticOrderAt F z
  rw [canonicalProductWithOrigin_analyticOrderAt H.originMultiplicity
    H.zeroData H.dyadicZeros.normProper z, H.analyticOrderAt_eq z]

/-- Dyadic divisor growth forces minimal quadratic type of the canonical
product. -/
theorem CompletedLFunctionHadamardData.canonicalProduct_logNormGrowth
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι) :
    HasSubquadraticLogNormGrowthAtInfinity H.canonicalProduct :=
  canonicalProductWithOrigin_hasSubquadraticLogNormGrowthAtInfinity
    H.originMultiplicity H.zeroData

/-- Nevanlinna-characteristic form of canonical-product minimal type. -/
theorem CompletedLFunctionHadamardData.canonicalProduct_characteristicGrowth
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι) :
    HasSubquadraticCharacteristicGrowthAtInfinity H.canonicalProduct :=
  canonicalProductWithOrigin_hasSubquadraticCharacteristicGrowthAtInfinity
    H.originMultiplicity H.zeroData H.dyadicZeros.normProper

/-- The origin contribution is nonpositive in the upper half-plane. -/
private theorem originMultiplicityResponse_im_nonpos
    (m : ℕ) (z : ℂ) (hz : 0 < z.im) :
    (((m : ℂ) / z).im) ≤ 0 := by
  rw [Complex.div_im]
  have hm_im : ((m : ℂ).im) = 0 := by simp
  have hm_re : ((m : ℂ).re) = (m : ℝ) := by simp
  rw [hm_im, hm_re]
  simp only [zero_mul, zero_div, zero_sub]
  exact neg_nonpos.mpr <| div_nonneg
    (mul_nonneg (Nat.cast_nonneg m) hz.le)
    (Complex.normSq_nonneg z)

/-- A nonzero origin multiplicity contributes strictly negatively. -/
private theorem originMultiplicityResponse_im_neg
    (m : ℕ) (hm : m ≠ 0) (z : ℂ) (hz : 0 < z.im) :
    (((m : ℂ) / z).im) < 0 := by
  rw [Complex.div_im]
  have hm_im : ((m : ℂ).im) = 0 := by simp
  have hm_re : ((m : ℂ).re) = (m : ℝ) := by simp
  rw [hm_im, hm_re]
  simp only [zero_mul, zero_div, zero_sub]
  apply neg_neg_of_pos
  apply div_pos
  · exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hz
  · exact Complex.normSq_pos.mpr (by
      intro hzero
      subst z
      simp at hz)

/-- If all zeros are real, the divisor expansion gives the strict
anti-Herglotz logarithmic-derivative sign. -/
theorem CompletedLFunctionHadamardData.strictAntiHerglotz_of_onlyRealZeros
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι)
    (hrealZeros : HasOnlyRealZeros F) :
    StrictAntiHerglotzUHP (logDerivativeResponse F) := by
  have hreal : ∀ i : ι, (H.zeroLoc i).im = 0 :=
    fun i ↦ hrealZeros (H.zeroLoc i) (H.zeroLoc_is_zero i)
  intro z hz
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp at hz
  have hzloc : ∀ i : ι, z ≠ H.zeroLoc i := by
    intro i hzi
    have him := congrArg Complex.im hzi
    rw [hreal i] at him
    linarith
  rw [H.logDerivative_expansion z hz0 hzloc]
  simp only [Complex.add_im, H.b_im, add_zero]
  rcases H.support_nonempty with hm | hι
  · exact add_neg_of_neg_of_nonpos
      (originMultiplicityResponse_im_neg H.originMultiplicity hm z hz)
      (hadamardRegularizedLogDerivSeries_im_nonpos_of_real_indexed
        H.zeroLoc H.zeroData hreal hz)
  · letI : Nonempty ι := hι
    exact add_neg_of_nonpos_of_neg
      (originMultiplicityResponse_im_nonpos H.originMultiplicity z hz)
      (hadamardRegularizedLogDerivSeries_im_neg_of_real_indexed
        H.zeroLoc H.zeroData hreal hz)

/-- Generic completed-L-function criterion: all zeros lie on the centered
critical line exactly when the logarithmic derivative is strictly
anti-Herglotz in the upper half-plane. -/
theorem CompletedLFunctionHadamardData.onlyRealZeros_iff_strictAntiHerglotz
    {F : ℂ → ℂ} {ι : Type u}
    (H : CompletedLFunctionHadamardData F ι) :
    HasOnlyRealZeros F ↔
      StrictAntiHerglotzUHP (logDerivativeResponse F) := by
  constructor
  · exact H.strictAntiHerglotz_of_onlyRealZeros
  · intro hstrict
    exact entire_function_roots_real_of_analytic_nontrivial F
      H.analytic H.nontrivial
      (fun z hz _hFz ↦ (hstrict z hz).le) H.schwarz

end OverflowResidueRH
