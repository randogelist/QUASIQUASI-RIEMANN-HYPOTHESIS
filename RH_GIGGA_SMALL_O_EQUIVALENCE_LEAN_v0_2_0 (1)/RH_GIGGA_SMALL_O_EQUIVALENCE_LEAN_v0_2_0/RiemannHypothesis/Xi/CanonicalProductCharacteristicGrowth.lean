/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.HadamardProduct.CanonicalProductGrowth
import RiemannHypothesis.HadamardProduct.CanonicalProductMultiplicity

/-!
# Growth of the canonical xi product

This module specializes the generic minimal-type genus-one product theorem to
the exact occurrence-indexed canonical divisor of the centered xi pullback.
-/

open Filter Metric Real Set Topology
open scoped Real

namespace OverflowResidueRH

open ValueDistribution

/-- The occurrence-indexed canonical xi product has pointwise logarithmic
growth `o(‖z‖²)` under its inverse-square zero-distribution theorem. -/
theorem entireXiPullbackCanonicalProduct_logNorm_subquadraticAtInfinity
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    HasSubquadraticLogNormGrowthAtInfinity
      entireXiPullbackCanonicalProduct := by
  change HasSubquadraticLogNormGrowthAtInfinity
    ((fun z : ℂ ↦ z ^ entireXiPullbackOriginMultiplicity) *
      infiniteHadamardProduct entireXiPullbackZeroOccurrenceLoc)
  exact
    (monomial_hasSubquadraticLogNormGrowthAtInfinity
      entireXiPullbackOriginMultiplicity).mul
      (infiniteHadamardProduct_hasSubquadraticLogNormGrowthAtInfinity
        H.toHadamardZeroInvSqSummability)

/-- The canonical xi product has subquadratic Nevanlinna characteristic
growth.  No extra growth or lower-bound hypothesis is required. -/
theorem entireXiPullbackCanonicalProduct_characteristic_subquadraticAtInfinity
    (H : EntireXiPullbackCanonicalZeroDistribution) :
    HasSubquadraticCharacteristicGrowthAtInfinity
      entireXiPullbackCanonicalProduct := by
  have hlog :=
    entireXiPullbackCanonicalProduct_logNorm_subquadraticAtInfinity H
  have hprox := hlog.toProximityGrowthAtInfinity
    (entireXiPullbackCanonicalProduct_differentiable H).continuous
  exact hprox.toCharacteristicGrowthAtInfinity_of_analytic
    (DifferentiableOn.analyticOnNhd
      (entireXiPullbackCanonicalProduct_differentiable H).differentiableOn
      isOpen_univ)

end OverflowResidueRH
