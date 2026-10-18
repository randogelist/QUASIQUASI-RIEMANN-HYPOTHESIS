/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.Xi.CanonicalQuotientCharacteristicGrowth
import RiemannHypothesis.Xi.EntireXiLogNormGrowth

/-!
# Unconditional count-side canonical quotient criterion

The concrete theta-kernel/Jensen construction supplies the canonical zero
distribution unconditionally.  Thus only the classical xi upper-growth bound
and the canonical-product characteristic estimate remain visible here.
-/

namespace OverflowResidueRH

/-- The actual theta-kernel/Jensen zero distribution, the classical xi upper
bound, and canonical-product characteristic growth imply strict Lagarias. -/
theorem
    riemannHypothesis_iff_lagarias_of_theta_xiLogNorm_productCharacteristic
    (hxi : HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (.of_xiLogNorm_and_productCharacteristic
      entireXiPullbackCanonicalZeroDistributionFromTheta hxi hproduct)

/-- Under the two remaining growth estimates, the concrete theta divisor
gives a constant-times-canonical-product factorization of centered xi. -/
theorem entireXiPullback_exists_constant_factorization_of_theta_growth
    (hxi : HasSubquadraticLogNormGrowthAtInfinity EntireXiPullback)
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ,
      EntireXiPullback z = c * entireXiPullbackCanonicalProduct z :=
  (EntireXiPullbackCanonicalQuotientLogNormGrowthData.of_xiLogNorm_and_productCharacteristic
    entireXiPullbackCanonicalZeroDistributionFromTheta hxi hproduct)
      |>.exists_constant_factorization

/-- The theta--Mellin analysis also discharges the xi numerator-growth field,
so only canonical-product characteristic growth remains. -/
theorem riemannHypothesis_iff_lagarias_of_theta_productCharacteristic
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_lagarias_of_theta_xiLogNorm_productCharacteristic
    entireXiPullback_hasSubquadraticLogNormGrowthAtInfinity hproduct

/-- Constant-times-product factorization with only the canonical-product
characteristic estimate left visible. -/
theorem entireXiPullback_exists_constant_factorization_of_theta_productCharacteristic
    (hproduct : HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ,
      EntireXiPullback z = c * entireXiPullbackCanonicalProduct z :=
  entireXiPullback_exists_constant_factorization_of_theta_growth
    entireXiPullback_hasSubquadraticLogNormGrowthAtInfinity hproduct

end OverflowResidueRH
