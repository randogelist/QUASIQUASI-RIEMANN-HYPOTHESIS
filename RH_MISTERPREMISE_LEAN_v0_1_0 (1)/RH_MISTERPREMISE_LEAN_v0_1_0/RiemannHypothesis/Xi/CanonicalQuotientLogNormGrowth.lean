/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import RiemannHypothesis.ComplexAnalysis.RealPartGrowth
import RiemannHypothesis.Xi.CanonicalProductSymmetry

/-!
# Canonical xi quotient: a maximum-modulus growth interface

The canonical quotient criterion originally exposes subquadratic norm growth
of a chosen entire logarithm.  Borel--Caratheodory shows that this asks for
more than the factorization argument needs: it is enough to bound

`log ‖entireXiPullbackCanonicalQuotient z‖`

from above by `o(‖z‖²)`.  No lower bound for the quotient, reciprocal-growth
estimate, or control of the imaginary part of a logarithm is required.

This file packages that sharper interface and feeds it into all three strict
RH criteria.  It also provides constructors from the equivalent
maximum-modulus estimate `‖q z‖ ≤ Aε exp (ε ‖z‖²)` and from ordinary finite
exponential type.
-/

namespace OverflowResidueRH

/-- The sharpened quotient-growth input: canonical divisor distribution and
only a one-sided logarithmic maximum-modulus estimate for the completed
quotient. -/
structure EntireXiPullbackCanonicalQuotientLogNormGrowthData : Type where
  zeroDistribution : EntireXiPullbackCanonicalZeroDistribution
  quotient_logNorm_subquadratic :
    HasSubquadraticLogNormGrowth entireXiPullbackCanonicalQuotient

/-- Borel--Caratheodory turns logarithmic maximum-modulus growth into the
full logarithm-growth package used by the existing quotient criterion. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.toQuotientGrowthData
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    EntireXiPullbackCanonicalQuotientGrowthData where
  zeroDistribution := H.zeroDistribution
  quotientLog_subquadratic :=
    H.quotient_logNorm_subquadratic.log_hasSubquadraticNormGrowth
      (entireXiPullbackCanonicalQuotientLog_differentiable H.zeroDistribution)
      (exp_entireXiPullbackCanonicalQuotientLog H.zeroDistribution)

/-- A subquadratic maximum-modulus estimate for the completed quotient
supplies the logarithmic maximum-modulus interface. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.of_exponentialNormGrowth
    (Hdist : EntireXiPullbackCanonicalZeroDistribution)
    (hgrowth :
      HasSubquadraticExponentialNormGrowth entireXiPullbackCanonicalQuotient) :
    EntireXiPullbackCanonicalQuotientLogNormGrowthData where
  zeroDistribution := Hdist
  quotient_logNorm_subquadratic :=
    hgrowth.toLogNormGrowth
      (entireXiPullbackCanonicalQuotient_ne_zero Hdist)

/-- Ordinary finite exponential type is already more than enough for the
completed quotient. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.of_linearExponentialNormGrowth
    (Hdist : EntireXiPullbackCanonicalZeroDistribution)
    (hgrowth : HasLinearExponentialNormGrowth
      entireXiPullbackCanonicalQuotient) :
    EntireXiPullbackCanonicalQuotientLogNormGrowthData :=
  .of_exponentialNormGrowth Hdist
    hgrowth.toSubquadraticExponentialNormGrowth

/-- A genuine at-infinity `o(‖z‖²)` bound is sufficient.  The fixed entire
quotient logarithm extends it over the omitted compact disk, so no global
constant has to be supplied by the analytic number-theory argument. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.of_logNormGrowthAtInfinity
    (Hdist : EntireXiPullbackCanonicalZeroDistribution)
    (hgrowth : HasSubquadraticLogNormGrowthAtInfinity
      entireXiPullbackCanonicalQuotient) :
    EntireXiPullbackCanonicalQuotientLogNormGrowthData where
  zeroDistribution := Hdist
  quotient_logNorm_subquadratic :=
    hgrowth.toGlobal_of_exp
      (entireXiPullbackCanonicalQuotientLog_differentiable Hdist).continuous
      (exp_entireXiPullbackCanonicalQuotientLog Hdist)

/-- The sharpened interface still forces the automatically constructed
quotient logarithm to be affine. -/
theorem
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.quotientLog_eq_affine
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    ∃ a b : ℂ, ∀ z : ℂ,
      entireXiPullbackCanonicalQuotientLog H.zeroDistribution z =
        a + b * z :=
  H.toQuotientGrowthData.quotientLog_eq_affine

/-- Evenness eliminates the linear term from the affine quotient logarithm.
Thus the completed canonical quotient is constant, not merely an exponential
of a general affine function. -/
theorem
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.quotientLog_eq_const
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    ∃ a : ℂ, ∀ z : ℂ,
      entireXiPullbackCanonicalQuotientLog H.zeroDistribution z = a := by
  obtain ⟨a, b, hab⟩ := H.quotientLog_eq_affine
  have heven :=
    entireXiPullbackCanonicalQuotientLog_neg H.zeroDistribution (1 : ℂ)
  rw [hab (-1), hab 1] at heven
  have hb : b = 0 := by
    linear_combination -heven / 2
  exact ⟨a, fun z ↦ by simpa [hb] using hab z⟩

/-- The sharpened one-sided growth bound yields the full canonical
affine-exponential factorization. -/
theorem
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.exists_factorization
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    ∃ a b : ℂ, ∀ z : ℂ,
      EntireXiPullback z = Complex.exp (a + b * z) *
        entireXiPullbackCanonicalProduct z :=
  H.toQuotientGrowthData.exists_factorization

/-- For the even centered xi pullback, the affine exponential ambiguity in
Hadamard factorization reduces to a single nonzero constant. -/
theorem
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.exists_constant_factorization
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℂ,
      EntireXiPullback z = c * entireXiPullbackCanonicalProduct z := by
  obtain ⟨a, ha⟩ := H.quotientLog_eq_const
  refine ⟨Complex.exp a, Complex.exp_ne_zero a, fun z ↦ ?_⟩
  rw [EntireXiPullback_eq_exp_canonicalQuotientLog_mul_canonicalProduct
    H.zeroDistribution z, ha z]

/-- Canonical logarithmic-derivative data from a one-sided quotient bound. -/
noncomputable def
    EntireXiPullbackCanonicalQuotientLogNormGrowthData.toCanonicalHadamardLogDerivativeData
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    EntireXiPullbackCanonicalHadamardLogDerivativeData :=
  H.toQuotientGrowthData.toCanonicalHadamardLogDerivativeData

/-- Pullback strict anti-Herglotz equivalence from a one-sided logarithmic
maximum-modulus bound. -/
theorem
    riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalQuotientLogNormGrowthData
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    RiemannHypothesis ↔ EntireXiPullback.StrictAntiHerglotzSign :=
  riemannHypothesis_iff_entireXiPullback_strictAntiHerglotz_of_canonicalQuotientGrowthData
    H.toQuotientGrowthData

/-- Right-half-plane strict logarithmic-derivative equivalence from the
sharpened quotient bound. -/
theorem
    riemannHypothesis_iff_entireXi_rightHalfPlaneSign_of_quotientLogNormGrowthData
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    RiemannHypothesis ↔ EntireXi.rightHalfPlaneStrictLogDerivSign :=
  riemannHypothesis_iff_entireXi_rightHalfPlaneStrictLogDerivSign_of_canonicalQuotientGrowthData
    H.toQuotientGrowthData

/-- Strict Lagarias equivalence from the sharpened one-sided quotient-growth
input. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (H : EntireXiPullbackCanonicalQuotientLogNormGrowthData) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientGrowthData
    H.toQuotientGrowthData

/-- Backlund--Turing plus the sharpened one-sided quotient bound. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_backlundTuring_and_quotientLogNormGrowth
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (hgrowth :
      HasSubquadraticLogNormGrowth entireXiPullbackCanonicalQuotient) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    { zeroDistribution := Hcount.toCanonicalZeroDistribution
      quotient_logNorm_subquadratic := hgrowth }

/-- Jensen/dyadic counting plus the sharpened one-sided quotient bound. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_dyadicCount_and_quotientLogNormGrowth
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (hgrowth :
      HasSubquadraticLogNormGrowth entireXiPullbackCanonicalQuotient) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    { zeroDistribution := Hcount.toCanonicalZeroDistribution
      quotient_logNorm_subquadratic := hgrowth }

/-- Backlund--Turing plus only the asymptotic logarithmic quotient estimate. -/
theorem
    riemannHypothesis_iff_lagarias_of_backlundTuring_and_quotientLogGrowthAtInfinity
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (hgrowth : HasSubquadraticLogNormGrowthAtInfinity
      entireXiPullbackCanonicalQuotient) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (.of_logNormGrowthAtInfinity
      Hcount.toCanonicalZeroDistribution hgrowth)

/-- Jensen/dyadic counting plus only the asymptotic logarithmic quotient
estimate. -/
theorem
    riemannHypothesis_iff_lagarias_of_dyadicCount_and_quotientLogGrowthAtInfinity
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (hgrowth : HasSubquadraticLogNormGrowthAtInfinity
      entireXiPullbackCanonicalQuotient) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (.of_logNormGrowthAtInfinity
      Hcount.toCanonicalZeroDistribution hgrowth)

/-- Backlund--Turing plus a direct subquadratic maximum-modulus estimate. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_backlundTuring_and_quotientMaxGrowth
    (Hcount : EntireXiPullbackCanonicalBacklundTuringHeightCountData)
    (hgrowth :
      HasSubquadraticExponentialNormGrowth entireXiPullbackCanonicalQuotient) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (.of_exponentialNormGrowth Hcount.toCanonicalZeroDistribution hgrowth)

/-- Jensen/dyadic counting plus a direct subquadratic maximum-modulus
estimate. -/
theorem
    riemannHypothesis_iff_entireXi_lagariasPositivity_of_dyadicCount_and_quotientMaxGrowth
    (Hcount : EntireXiPullbackDyadicCumulativeCountData)
    (hgrowth :
      HasSubquadraticExponentialNormGrowth entireXiPullbackCanonicalQuotient) :
    RiemannHypothesis ↔ EntireXi.LagariasPositivity :=
  riemannHypothesis_iff_entireXi_lagariasPositivity_of_canonicalQuotientLogNormGrowthData
    (.of_exponentialNormGrowth Hcount.toCanonicalZeroDistribution hgrowth)

end OverflowResidueRH
