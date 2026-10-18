/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.Xi.CanonicalProductCharacteristicGrowth
import RiemannHypothesis.Xi.CanonicalQuotientThetaCharacteristicGrowth

/-!
# The unconditional Riemann xi--Lagarias equivalence

The theta--Mellin/Jensen route supplies the canonical zero distribution and
subquadratic logarithmic growth of the actual xi pullback.  Inverse-square
summability supplies minimal-type growth of the associated genus-one product.
The First Main Theorem, Poisson's formula, Borel--Caratheodory, and Cauchy
rigidity then identify xi with that product up to a nonzero constant and yield
the classical strict logarithmic-derivative criterion with no auxiliary
hypotheses.

This is an equivalence with the Riemann hypothesis, not a proof of either side.
-/

namespace OverflowResidueRH

/-- Fully constructed one-sided quotient-growth data for the actual xi
pullback and its canonical analytic-order divisor. -/
noncomputable def entireXiPullbackCanonicalQuotientLogNormGrowthDataUnconditional :
    EntireXiPullbackCanonicalQuotientLogNormGrowthData :=
  .of_xiLogNorm_and_productCharacteristic
    entireXiPullbackCanonicalZeroDistributionFromTheta
    entireXiPullback_hasSubquadraticLogNormGrowthAtInfinity
    (entireXiPullbackCanonicalProduct_characteristic_subquadraticAtInfinity
      entireXiPullbackCanonicalZeroDistributionFromTheta)

/-- The canonical logarithmic-derivative expansion package for xi, with no
unproved count, factorization, or growth field. -/
noncomputable def entireXiPullbackCanonicalHadamardLogDerivativeDataUnconditional :
    EntireXiPullbackCanonicalHadamardLogDerivativeData :=
  entireXiPullbackCanonicalQuotientLogNormGrowthDataUnconditional
    |>.toCanonicalHadamardLogDerivativeData

/-- Unconditional constant-times-canonical-product factorization of the
centered Riemann xi pullback. -/
theorem entireXiPullback_exists_constant_factorization_unconditional :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ,
      EntireXiPullback z = c * entireXiPullbackCanonicalProduct z :=
  entireXiPullbackCanonicalQuotientLogNormGrowthDataUnconditional
    |>.exists_constant_factorization

/-- The punctured canonical logarithmic-derivative expansion for the actual
xi pullback.  Negation symmetry has removed the affine constant term. -/
theorem entireXiPullback_logDerivative_canonicalExpansion_unconditional
    (z : ℂ) (hz0 : z ≠ 0)
    (hzloc : ∀ i : EntireXiPullbackZeroOccurrence,
      z ≠ entireXiPullbackZeroOccurrenceLoc i) :
    logDerivativeResponse EntireXiPullback z =
      (entireXiPullbackOriginMultiplicity : ℂ) / z +
        hadamardRegularizedLogDerivSeries
          entireXiPullbackZeroOccurrenceLoc z := by
  let H := entireXiPullbackCanonicalHadamardLogDerivativeDataUnconditional
  have hexp := H.logDerivative_expansion z hz0 hzloc
  rw [H.b_eq_zero] at hexp
  simpa using hexp

/-- Assumption-free strict anti-Herglotz characterization of Mathlib's RH by
the critical-line pullback. -/
theorem riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_unconditional :
    RiemannHypothesis ↔ EntireXiPullback.StrictAntiHerglotzSign :=
  riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalQuotientLogNormGrowthData
    entireXiPullbackCanonicalQuotientLogNormGrowthDataUnconditional

/-- Assumption-free right-half-plane strict logarithmic-derivative
characterization of Mathlib's RH. -/
theorem
    riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_unconditional :
    RiemannHypothesis ↔ EntireXi.rightHalfPlaneStrictLogDerivSign :=
  riemannHypothesis_iff_entireXi_rightHalfPlaneSign_of_quotientLogNormGrowthData
    entireXiPullbackCanonicalQuotientLogNormGrowthDataUnconditional

/-- Fully formalized classical strict Lagarias equivalence for Mathlib's
literal Riemann hypothesis.  No auxiliary analytic hypothesis remains. -/
theorem riemannHypothesis_iff_entireXi_lagariasPositivity_unconditional :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    entireXiPullbackCanonicalQuotientLogNormGrowthDataUnconditional

end OverflowResidueRH
