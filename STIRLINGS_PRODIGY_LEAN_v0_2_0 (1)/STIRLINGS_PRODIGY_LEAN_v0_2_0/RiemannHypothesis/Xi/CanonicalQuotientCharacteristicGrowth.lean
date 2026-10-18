/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.ComplexAnalysis.ProximityGrowth
import RiemannHypothesis.Xi.CanonicalQuotientLogNormGrowth

/-!
# Canonical xi quotient growth from Nevanlinna characteristics

This module replaces a pointwise lower bound for the canonical product by
upper Nevanlinna characteristic bounds for the numerator and denominator.
The First Main Theorem controls the quotient's circle-average proximity even
at common zeros.  Poisson's formula then gives the one-sided pointwise
logarithmic quotient bound needed by Borel--Caratheodory and Cauchy rigidity.

The two characteristic hypotheses are deliberately visible fields.  In the
xi application the product field should follow from inverse-square summability
of its divisor, while the numerator field is the classical finite-order
estimate for the completed xi function.
-/

open Filter Set
open ValueDistribution

namespace OverflowResidueRH

/-- The canonical zero distribution together with subquadratic Nevanlinna
characteristics for the centered xi pullback and its canonical product. -/
structure EntireXiPullbackCanonicalCharacteristicGrowthData : Type where
  zeroDistribution : EntireXiPullbackCanonicalZeroDistribution
  xi_characteristic_subquadratic :
    HasSubquadraticCharacteristicGrowthAtInfinity EntireXiPullback
  canonicalProduct_characteristic_subquadratic :
    HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct

private theorem canonicalProduct_I_div_two_ne_zero
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    entireXiPullbackCanonicalProduct (Complex.I / 2) ≠ 0 := by
  have hF : EntireXiPullback (Complex.I / 2) ≠ 0 := by
    rw [EntireXiPullback_apply_I_div_two]
    norm_num
  apply entireXiPullbackCanonicalProduct_ne_zero_of_away H
  · exact div_ne_zero Complex.I_ne_zero (by norm_num)
  · intro i hi
    apply hF
    rw [hi]
    exact entireXiPullbackZeroOccurrenceLoc_is_zero i

/-- The xi numerator only needs subquadratic proximity; the stronger
characteristic bound is needed solely for the denominator because division
introduces its zeros as poles. -/
theorem
    entireXiPullbackCanonicalQuotient_proximity_subquadratic_of_xiProximity
    (Hdist : EntireXiPullbackCanonicalZeroDistribution)
    (hxi : HasSubquadraticProximityGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    HasSubquadraticProximityGrowthAtInfinity
      entireXiPullbackCanonicalQuotient := by
  have hFmer : Meromorphic EntireXiPullback := fun z ↦
    (EntireXiPullback_analyticAt z).meromorphicAt
  have hPmer : Meromorphic entireXiPullbackCanonicalProduct := fun z ↦
    (entireXiPullbackCanonicalProduct_differentiable
      Hdist).analyticAt z |>.meromorphicAt
  have hPcodiscrete :
      entireXiPullbackCanonicalProduct ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    (DifferentiableOn.analyticOnNhd
      (entireXiPullbackCanonicalProduct_differentiable
        Hdist).differentiableOn isOpen_univ)
      |>.preimage_zero_mem_codiscrete
        (canonicalProduct_I_div_two_ne_zero Hdist)
  have hquot : entireXiPullbackCanonicalQuotient =ᶠ[codiscrete ℂ]
      EntireXiPullback * entireXiPullbackCanonicalProduct⁻¹ := by
    filter_upwards [hPcodiscrete] with z hz
    have hz' : entireXiPullbackCanonicalProduct z ≠ 0 := by
      simpa using hz
    rw [entireXiPullbackCanonicalQuotient_eq_div Hdist hz']
    rfl
  exact
    hasSubquadraticProximityGrowthAtInfinity_of_proximity_and_characteristic
      hFmer hPmer hquot hxi hproduct

/-- A classical pointwise upper growth estimate for xi, together with
characteristic control of the canonical product, gives the quotient estimate
at infinity. -/
theorem
    entireXiPullbackCanonicalQuotient_logNorm_subquadraticAtInfinity_of_xiLogNorm
    (Hdist : EntireXiPullbackCanonicalZeroDistribution)
    (hxi : HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    HasSubquadraticLogNormGrowthAtInfinity
      entireXiPullbackCanonicalQuotient :=
  (entireXiPullbackCanonicalQuotient_proximity_subquadratic_of_xiProximity
      Hdist
      (hxi.toProximityGrowthAtInfinity EntireXiPullback_differentiable.continuous)
      hproduct).toLogNormGrowthAtInfinity
    (entireXiPullbackCanonicalQuotientLog_differentiable Hdist)
    (exp_entireXiPullbackCanonicalQuotientLog Hdist)

/-- Construct the quotient-growth package directly from the classical xi
upper bound and the canonical-product characteristic estimate. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.of_xiLogNorm_and_productCharacteristic
    (Hdist : EntireXiPullbackCanonicalZeroDistribution)
    (hxi : HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    EntireXiPullbackCanonicalQuotientLogNormGrowthData :=
  .of_logNormGrowthAtInfinity Hdist
    (entireXiPullbackCanonicalQuotient_logNorm_subquadraticAtInfinity_of_xiLogNorm
      Hdist hxi hproduct)

/-- Characteristic control of xi and the canonical product gives
subquadratic proximity of their completed quotient. -/
theorem
    EntireXiPullbackCanonicalCharacteristicGrowthData.quotient_proximity_subquadratic
    (H : EntireXiPullbackCanonicalCharacteristicGrowthData) :
    HasSubquadraticProximityGrowthAtInfinity
      entireXiPullbackCanonicalQuotient := by
  have hFmer : Meromorphic EntireXiPullback := fun z ↦
    (EntireXiPullback_analyticAt z).meromorphicAt
  have hPmer : Meromorphic entireXiPullbackCanonicalProduct := fun z ↦
    (entireXiPullbackCanonicalProduct_differentiable
      H.zeroDistribution).analyticAt z |>.meromorphicAt
  have hPcodiscrete :
      entireXiPullbackCanonicalProduct ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    (DifferentiableOn.analyticOnNhd
      (entireXiPullbackCanonicalProduct_differentiable
        H.zeroDistribution).differentiableOn isOpen_univ)
      |>.preimage_zero_mem_codiscrete
        (canonicalProduct_I_div_two_ne_zero H.zeroDistribution)
  have hquot : entireXiPullbackCanonicalQuotient =ᶠ[codiscrete ℂ]
      EntireXiPullback * entireXiPullbackCanonicalProduct⁻¹ := by
    filter_upwards [hPcodiscrete] with z hz
    have hz' : entireXiPullbackCanonicalProduct z ≠ 0 := by
      simpa using hz
    rw [entireXiPullbackCanonicalQuotient_eq_div H.zeroDistribution hz']
    rfl
  exact
    hasSubquadraticProximityGrowthAtInfinity_of_characteristic_factors
      hFmer hPmer hquot H.xi_characteristic_subquadratic
        H.canonicalProduct_characteristic_subquadratic

/-- Poisson's formula upgrades quotient proximity to the pointwise
`o(‖z‖²)` logarithmic norm estimate at infinity. -/
theorem
    EntireXiPullbackCanonicalCharacteristicGrowthData.quotient_logNorm_subquadraticAtInfinity
    (H : EntireXiPullbackCanonicalCharacteristicGrowthData) :
    HasSubquadraticLogNormGrowthAtInfinity
      entireXiPullbackCanonicalQuotient :=
  H.quotient_proximity_subquadratic.toLogNormGrowthAtInfinity
    (entireXiPullbackCanonicalQuotientLog_differentiable
      H.zeroDistribution)
    (exp_entireXiPullbackCanonicalQuotientLog H.zeroDistribution)

/-- The characteristic package supplies the maximum-modulus quotient-growth
interface without any denominator lower bound. -/
noncomputable def
    EntireXiPullbackCanonicalCharacteristicGrowthData.toQuotientLogNormGrowthData
    (H : EntireXiPullbackCanonicalCharacteristicGrowthData) :
    EntireXiPullbackCanonicalQuotientLogNormGrowthData :=
  .of_logNormGrowthAtInfinity H.zeroDistribution
    H.quotient_logNorm_subquadraticAtInfinity

/-- Characteristic growth yields the constant-times-canonical-product
Hadamard factorization appropriate to the even centered xi pullback. -/
theorem
    EntireXiPullbackCanonicalCharacteristicGrowthData.exists_constant_factorization
    (H : EntireXiPullbackCanonicalCharacteristicGrowthData) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ,
      EntireXiPullback z = c * entireXiPullbackCanonicalProduct z :=
  H.toQuotientLogNormGrowthData.exists_constant_factorization

/-- Strict Lagarias equivalence from canonical zero distribution and the two
subquadratic characteristic bounds. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalCharacteristicGrowthData
    (H : EntireXiPullbackCanonicalCharacteristicGrowthData) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    H.toQuotientLogNormGrowthData

/-- Backlund--Turing zero counting plus the two characteristic estimates. -/
theorem
    riemannHypothesis_iff_lagarias_of_backlundTuring_and_characteristicGrowth
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (hxi : HasSubquadraticCharacteristicGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalCharacteristicGrowthData
    { zeroDistribution := Hcount.toCanonicalZeroDistribution
      xi_characteristic_subquadratic := hxi
      canonicalProduct_characteristic_subquadratic := hproduct }

/-- Jensen/dyadic zero counting plus the two characteristic estimates. -/
theorem
    riemannHypothesis_iff_lagarias_of_dyadicCount_and_characteristicGrowth
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (hxi : HasSubquadraticCharacteristicGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalCharacteristicGrowthData
    { zeroDistribution := Hcount.toCanonicalZeroDistribution
      xi_characteristic_subquadratic := hxi
      canonicalProduct_characteristic_subquadratic := hproduct }

/-- Backlund--Turing zero counting, the classical pointwise xi upper-growth
bound, and canonical-product characteristic growth imply the strict Lagarias
equivalence. -/
theorem
    riemannHypothesis_iff_lagarias_of_backlundTuring_xiLogNorm_productCharacteristic
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (hxi : HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (.of_xiLogNorm_and_productCharacteristic
      Hcount.toCanonicalZeroDistribution hxi hproduct)

/-- Jensen/dyadic zero counting, the classical pointwise xi upper-growth
bound, and canonical-product characteristic growth imply the strict Lagarias
equivalence. -/
theorem
    riemannHypothesis_iff_lagarias_of_dyadicCount_xiLogNorm_productCharacteristic
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (hxi : HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (.of_xiLogNorm_and_productCharacteristic
      Hcount.toCanonicalZeroDistribution hxi hproduct)

end OverflowResidueRH
